#!/usr/bin/env python3
"""
Minimal GUI MIDI -> solenoid player (Raspberry Pi 5) with LED controls.

- Window sized for 800x480 (under top taskbar), dark theme.
- Pause / Stop Current / Exit; Search; Add All (Random); Add to Queue.
- Position slider uses press/release + periodic update (multiple seeks work), resets after a song.
- Pausing/stopping hard-cuts all solenoids over I2C and clears LEDs.
- Volume slider (centered row) with "Volume" (left) and percentage (right); persisted to player_config.json.
- Fluidsynth audio playback in parallel; seeks trim MIDI so audio stays in sync.
- Resume is instantaneous; slider stays in sync after pauses.
- NEW (back): LED Light Controls (RGB, Brightness, Effect) under Loop/Shuffle/Audio.
  LEDs update at 20 Hz on a background thread and mirror active notes.
"""

import asyncio
import csv
import json
import os
import signal
import sys
import threading
import time
import random
import re
import queue
import tkinter as tk
from tkinter import ttk, messagebox, filedialog
import subprocess
import tempfile
import concurrent.futures
import multiprocessing
import struct
from multiprocessing import shared_memory
import math
from bisect import bisect_right
from typing import Optional, Tuple
from datetime import datetime

import mido
import pretty_midi

import board
import busio
from adafruit_pca9685 import PCA9685

from watchdog.observers import Observer
from watchdog.events import FileSystemEventHandler


# ----- Optional NeoPixel strip driver for Pi 5 -----
from pi5neo import Pi5Neo  # expects: set_led_color(i,r,g,b), update_strip(), fill_strip(r,g,b)

# --------- PATHS / CONFIG ---------
# Runtime configuration lives in player_config.json by default.
# PIANOPI_CONFIG can point at a different JSON file if you enjoy variety.
CONFIG_FILE = os.environ.get(
    "PIANOPI_CONFIG",
    os.path.join(os.path.dirname(__file__), "player_config.json"),
)


def _read_startup_config() -> dict:
    try:
        with open(CONFIG_FILE, "r") as f:
            data = json.load(f)
            return data if isinstance(data, dict) else {}
    except Exception:
        return {}


def _startup_bool(name: str, default=False) -> bool:
    value = os.environ.get(f"PIANOPI_{name.upper()}", _STARTUP_CFG.get(name, default))
    if isinstance(value, bool):
        return value
    if isinstance(value, (int, float)):
        return bool(value)
    return str(value).strip().lower() in ("1", "true", "yes", "on")


_STARTUP_CFG = _read_startup_config()

MIDI_DIR = os.path.expanduser(
    os.environ.get(
        "PIANOPI_MIDI_DIR",
        _STARTUP_CFG.get("midi_dir", "/home/pi5/Desktop/midiMusicFiles"),
    )
)

KEYBOARD_RECORDINGS_DIR = os.path.join(MIDI_DIR, "Keyboard Recordings")
KEYBOARD_RECORDINGS_INDEX_FILE = os.path.join(KEYBOARD_RECORDINGS_DIR, "recordings_index.json")
DEFAULT_RECORDING_PROGRAM = 1  # GM 002 Bright Acoustic Piano, because GM is zero-based and mildly cruel.
TICKS_PER_BEAT = 480
DEFAULT_TEMPO = 500000  # 120 BPM
FIRST_NOTE = 21   # A0, first key on an 88-key piano
LAST_NOTE = 108   # C8, last key on an 88-key piano

GENERAL_MIDI_PROGRAMS = [
    "Acoustic Grand Piano", "Bright Acoustic Piano", "Electric Grand Piano", "Honky-tonk Piano",
    "Electric Piano 1", "Electric Piano 2", "Harpsichord", "Clavinet",
    "Celesta", "Glockenspiel", "Music Box", "Vibraphone",
    "Marimba", "Xylophone", "Tubular Bells", "Dulcimer",
    "Drawbar Organ", "Percussive Organ", "Rock Organ", "Church Organ",
    "Reed Organ", "Accordion", "Harmonica", "Tango Accordion",
    "Acoustic Guitar (nylon)", "Acoustic Guitar (steel)", "Electric Guitar (jazz)", "Electric Guitar (clean)",
    "Electric Guitar (muted)", "Overdriven Guitar", "Distortion Guitar", "Guitar Harmonics",
    "Acoustic Bass", "Electric Bass (finger)", "Electric Bass (pick)", "Fretless Bass",
    "Slap Bass 1", "Slap Bass 2", "Synth Bass 1", "Synth Bass 2",
    "Violin", "Viola", "Cello", "Contrabass",
    "Tremolo Strings", "Pizzicato Strings", "Orchestral Harp", "Timpani",
    "String Ensemble 1", "String Ensemble 2", "Synth Strings 1", "Synth Strings 2",
    "Choir Aahs", "Voice Oohs", "Synth Voice", "Orchestra Hit",
    "Trumpet", "Trombone", "Tuba", "Muted Trumpet",
    "French Horn", "Brass Section", "Synth Brass 1", "Synth Brass 2",
    "Soprano Sax", "Alto Sax", "Tenor Sax", "Baritone Sax",
    "Oboe", "English Horn", "Bassoon", "Clarinet",
    "Piccolo", "Flute", "Recorder", "Pan Flute",
    "Blown Bottle", "Shakuhachi", "Whistle", "Ocarina",
    "Lead 1 (square)", "Lead 2 (sawtooth)", "Lead 3 (calliope)", "Lead 4 (chiff)",
    "Lead 5 (charang)", "Lead 6 (voice)", "Lead 7 (fifths)", "Lead 8 (bass + lead)",
    "Pad 1 (new age)", "Pad 2 (warm)", "Pad 3 (polysynth)", "Pad 4 (choir)",
    "Pad 5 (bowed)", "Pad 6 (metallic)", "Pad 7 (halo)", "Pad 8 (sweep)",
    "FX 1 (rain)", "FX 2 (soundtrack)", "FX 3 (crystal)", "FX 4 (atmosphere)",
    "FX 5 (brightness)", "FX 6 (goblins)", "FX 7 (echoes)", "FX 8 (sci-fi)",
    "Sitar", "Banjo", "Shamisen", "Koto",
    "Kalimba", "Bagpipe", "Fiddle", "Shanai",
    "Tinkle Bell", "Agogo", "Steel Drums", "Woodblock",
    "Taiko Drum", "Melodic Tom", "Synth Drum", "Reverse Cymbal",
    "Guitar Fret Noise", "Breath Noise", "Seashore", "Bird Tweet",
    "Telephone Ring", "Helicopter", "Applause", "Gunshot",
]
SOUND_FONT = os.path.expanduser(
    os.environ.get(
        "PIANOPI_SOUND_FONT",
        _STARTUP_CFG.get("sound_font", "/usr/share/sounds/sf2/FluidR3_GM.sf2"),
    )
)  # Fluidsynth GM soundfont
LED_CONFIG_FILE = os.path.join(os.path.dirname(__file__), "led_config.json")
INSTRUMENT_FILTERS_FILE = os.path.join(os.path.dirname(__file__), "instrument_filters.json")
PLAY_HISTORY_CSV_FILE = os.path.join(os.path.dirname(__file__), "song_play_history.csv")
APP_VERSION = str(_STARTUP_CFG.get("app_version", "2026.07.04.2-github"))
# Arm physical playback slightly in the future so prepared FluidSynth audio,
# the visualizer clock, and the solenoid scheduler start together.
AUDIO_SYNC_ARM_DELAY = float(_STARTUP_CFG.get("audio_sync_arm_delay", 0.18))
# Flask/web control binding. 0.0.0.0 means devices on your LAN can connect to
# http://<pi-ip>:8000/. Keep this on a trusted local network; there is no login.
WEB_HOST = str(os.environ.get("PIANOPI_WEB_HOST", _STARTUP_CFG.get("web_host", "0.0.0.0")))
WEB_PORT = int(os.environ.get("PIANOPI_WEB_PORT", _STARTUP_CFG.get("web_port", 8000)))
# ----------------------------------

# --------- HARDWARE MODE ---------
# real_piano = true when the robot is installed on a real acoustic piano.
# real_piano = false when using the keyboard test rig.
REAL_PIANO = 1 if _startup_bool("real_piano", False) else 0

# When true, the on-screen keyboard opens when the Search field is focused
# and closes when Search loses focus or Enter/Escape is pressed.
TOUCHSCREEN_OSK_AUTO_SHOW = _startup_bool("touchscreen_osk_auto_show", True)
# ---------------------------------

# --------- CONFIG PERSISTENCE ---------
def _read_config() -> dict:
    try:
        with open(CONFIG_FILE, "r") as f:
            data = json.load(f)
            return data if isinstance(data, dict) else {}
    except Exception:
        return {}

def _write_config(cfg: dict) -> None:
    try:
        with open(CONFIG_FILE, "w") as f:
            json.dump(cfg, f)
    except Exception as e:
        print(f"[WARN] Could not write config: {e}")


class BackgroundSongPlayLogger:
    """Append song-start rows to CSV without blocking the Tk/solenoid threads."""

    FIELDNAMES = [
        "started_at",
        "song_title",
        "filename",
        "file_path",
        "start_offset_seconds",
    ]

    def __init__(self, csv_path: str):
        self.csv_path = csv_path
        self._queue = queue.Queue()
        self._stop_event = threading.Event()
        self._thread = threading.Thread(target=self._run, daemon=True)
        self._started = False

    def start(self):
        if not self._started:
            self._started = True
            self._thread.start()

    def log_song_start(self, song_path: str, start_offset: float = 0.0):
        """Queue a song-start row. This returns immediately."""
        try:
            path = _safe_abs(song_path)
            filename = os.path.basename(path)
            title = os.path.splitext(filename)[0]
            row = {
                "started_at": datetime.now().astimezone().isoformat(timespec="seconds"),
                "song_title": title,
                "filename": filename,
                "file_path": path,
                "start_offset_seconds": f"{float(start_offset):.3f}",
            }
            self._queue.put_nowait(row)
        except Exception as e:
            print(f"[WARN] Could not queue song play log row: {e}")

    def stop(self, timeout: float = 0.75):
        try:
            self._stop_event.set()
            self._queue.put_nowait(None)
            if self._started and self._thread.is_alive():
                self._thread.join(timeout=timeout)
        except Exception:
            pass

    def _run(self):
        while True:
            try:
                item = self._queue.get(timeout=0.25)
            except queue.Empty:
                if self._stop_event.is_set():
                    break
                continue

            if item is None:
                if self._stop_event.is_set():
                    break
                continue

            try:
                self._append_row(item)
            except Exception as e:
                # Logging should never disturb playback. Humans hate silence, apparently.
                print(f"[WARN] Could not append song play log row: {e}")

    def _append_row(self, row: dict):
        folder = os.path.dirname(self.csv_path)
        if folder:
            os.makedirs(folder, exist_ok=True)
        needs_header = not os.path.exists(self.csv_path) or os.path.getsize(self.csv_path) == 0
        with open(self.csv_path, "a", newline="", encoding="utf-8") as f:
            writer = csv.DictWriter(f, fieldnames=self.FIELDNAMES)
            if needs_header:
                writer.writeheader()
            writer.writerow({name: row.get(name, "") for name in self.FIELDNAMES})
            f.flush()



def _safe_abs(path: str) -> str:
    try:
        return os.path.abspath(os.path.expanduser(str(path)))
    except Exception:
        return os.path.abspath(str(path))


def _is_inside_folder(path: str, folder: str) -> bool:
    try:
        path_abs = _safe_abs(path)
        folder_abs = _safe_abs(folder)
        return os.path.commonpath([path_abs, folder_abs]) == folder_abs
    except Exception:
        return False


def _is_keyboard_recording_path(path: str) -> bool:
    return _is_inside_folder(path, KEYBOARD_RECORDINGS_DIR)


def _read_recordings_index() -> dict:
    try:
        with open(KEYBOARD_RECORDINGS_INDEX_FILE, "r") as f:
            data = json.load(f)
        return data if isinstance(data, dict) else {}
    except Exception:
        return {}


def _write_recordings_index(data: dict) -> None:
    try:
        os.makedirs(KEYBOARD_RECORDINGS_DIR, exist_ok=True)
        with open(KEYBOARD_RECORDINGS_INDEX_FILE, "w") as f:
            json.dump(data if isinstance(data, dict) else {}, f, indent=2)
    except Exception as e:
        print(f"[WARN] Could not write recordings index: {e}")


def _recording_index_key(path: str) -> str:
    try:
        return os.path.relpath(_safe_abs(path), _safe_abs(KEYBOARD_RECORDINGS_DIR)).replace(os.sep, "/")
    except Exception:
        return _safe_abs(path)


def _get_keyboard_recording_metadata(path: str) -> dict:
    data = _read_recordings_index()
    entry = data.get(_recording_index_key(path), {})
    return entry if isinstance(entry, dict) else {}


def _update_keyboard_recording_metadata(path: str, **updates) -> None:
    data = _read_recordings_index()
    key = _recording_index_key(path)
    entry = data.get(key, {})
    if not isinstance(entry, dict):
        entry = {}
    entry.update(updates)
    entry.setdefault("path", key)
    entry.setdefault("source", "keyboard_recording")
    data[key] = entry
    _write_recordings_index(data)


def _move_keyboard_recording_metadata(old_path: str, new_path: str) -> None:
    data = _read_recordings_index()
    old_key = _recording_index_key(old_path)
    new_key = _recording_index_key(new_path)
    entry = data.pop(old_key, {})
    if not isinstance(entry, dict):
        entry = {}
    if entry:
        entry["path"] = new_key
        entry["renamed_at"] = time.strftime("%Y-%m-%d %H:%M:%S")
        data[new_key] = entry
    _write_recordings_index(data)


def _delete_keyboard_recording_metadata(path: str) -> None:
    data = _read_recordings_index()
    key = _recording_index_key(path)
    if key in data:
        data.pop(key, None)
        _write_recordings_index(data)


def _move_instrument_filter_key(old_path: str, new_path: str) -> None:
    store = _read_instrument_filters()
    old_key = _song_filter_key(old_path)
    new_key = _song_filter_key(new_path)
    if old_key in store:
        store[new_key] = store.pop(old_key)
        _write_instrument_filters(store)


def _delete_instrument_filter_key(path: str) -> None:
    store = _read_instrument_filters()
    key = _song_filter_key(path)
    if key in store:
        store.pop(key, None)
        _write_instrument_filters(store)


def _first_program_in_midi(path: str, default: int = DEFAULT_RECORDING_PROGRAM) -> int:
    try:
        mid = mido.MidiFile(path, clip=True)
        for track in mid.tracks:
            for msg in track:
                if not getattr(msg, "is_meta", False) and msg.type == "program_change":
                    return max(0, min(127, int(msg.program)))
    except Exception:
        pass
    return int(default)


def set_keyboard_recording_instrument(path: str, program: int) -> None:
    """Replace/insert the channel-0 GM program at the start of a saved keyboard recording."""
    program = max(0, min(127, int(program)))
    mid = mido.MidiFile(path, clip=True)
    if not mid.tracks:
        mid.tracks.append(mido.MidiTrack())
    track = mid.tracks[0]

    # Prefer replacing an existing zero-time channel-0 program change.
    abs_ticks = 0
    for msg in track:
        try:
            abs_ticks += int(getattr(msg, "time", 0) or 0)
        except Exception:
            pass
        if (
            not getattr(msg, "is_meta", False)
            and msg.type == "program_change"
            and getattr(msg, "channel", 0) == 0
            and abs_ticks == 0
        ):
            msg.program = program
            mid.save(path)
            _update_keyboard_recording_metadata(path, instrument=program, instrument_name=GENERAL_MIDI_PROGRAMS[program])
            return

    # Insert after any leading zero-time meta events, such as tempo.
    insert_at = 0
    for i, msg in enumerate(track):
        if getattr(msg, "is_meta", False) and getattr(msg, "time", 0) == 0:
            insert_at = i + 1
            continue
        break

    track.insert(insert_at, mido.Message("program_change", channel=0, program=program, time=0))
    mid.save(path)
    _update_keyboard_recording_metadata(path, instrument=program, instrument_name=GENERAL_MIDI_PROGRAMS[program])

def _read_led_config() -> dict:
    try:
        with open(LED_CONFIG_FILE, "r") as f:
            data = json.load(f)
            if not isinstance(data, dict):
                raise ValueError("bad led config")
    except Exception:
        data = {
            "red": 100, "green": 100, "blue": 100,
            "brightness": 100,
            "effect": "Solid",
            "idle_effect": "Off",   # <-- NEW
            "speed": 20             # <-- for idle patterns
        }
    return data

def _write_led_config(cfg: dict) -> None:
    try:
        with open(LED_CONFIG_FILE, "w") as f:
            json.dump(cfg, f)
    except Exception as e:
        print(f"[WARN] Could not write LED config: {e}")

def _set_touchscreen_keyboard_visible(visible: bool) -> None:
    """Show/hide Raspberry Pi OS Squeekboard through D-Bus, if enabled."""
    if not TOUCHSCREEN_OSK_AUTO_SHOW:
        return

    try:
        subprocess.run(
            [
                "busctl", "--user", "call",
                "sm.puri.OSK0",
                "/sm/puri/OSK0",
                "sm.puri.OSK0",
                "SetVisible",
                "b",
                "true" if visible else "false",
            ],
            stdout=subprocess.DEVNULL,
            stderr=subprocess.DEVNULL,
            timeout=1.0,
            check=False,
        )
    except Exception as exc:
        print(f"[WARN] Could not control on-screen keyboard: {exc}")


_cfg = _read_config()
_led_cfg = _read_led_config()

# If Rush/black-MIDI density makes the hardware scheduler fall behind, skip
# stale note-on events instead of playing a late backlog after the song is over.
# Note-off events still run when needed so coils do not get stuck on.
PHYSICAL_MAX_EVENT_LAG = float(_cfg.get("physical_max_event_lag", 0.12))
PHYSICAL_END_GRACE = float(_cfg.get("physical_end_grace", 0.02))
PHYSICAL_LAG_SKIP_ENABLED = bool(_cfg.get("physical_lag_skip_enabled", False))
# --------------------------------------



# --------- SYSTEM AUDIO BOOSTER (pactl) ---------
# Controls the default PipeWire/PulseAudio sink from inside the player.
# This replaces the separate loud_volume_gui.py window.
AUDIO_BOOST_MAX_VOLUME = 400
AUDIO_BOOST_STEP = 5
_AUDIO_BOOST_VOLUME_RE = re.compile(r"/\s*([0-9]+)%")


def _audio_boost_run_cmd(args):
    try:
        result = subprocess.run(
            args,
            check=True,
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
        )
        return result.stdout.strip()
    except FileNotFoundError:
        raise RuntimeError("pactl was not found")
    except subprocess.CalledProcessError as exc:
        msg = exc.stderr.strip() or exc.stdout.strip() or str(exc)
        raise RuntimeError(msg)


def _audio_boost_get_default_sink():
    return _audio_boost_run_cmd(["pactl", "get-default-sink"])


def _audio_boost_get_sink_volume_percent():
    output = _audio_boost_run_cmd(["pactl", "get-sink-volume", "@DEFAULT_SINK@"])
    matches = _AUDIO_BOOST_VOLUME_RE.findall(output)
    if not matches:
        raise RuntimeError(f"Could not parse pactl volume output: {output}")
    values = [int(x) for x in matches]
    return round(sum(values) / len(values))


def _audio_boost_set_sink_volume_percent(percent):
    percent = max(0, int(round(percent)))
    _audio_boost_run_cmd(["pactl", "set-sink-volume", "@DEFAULT_SINK@", f"{percent}%"])


def _audio_boost_set_sink_mute(muted):
    _audio_boost_run_cmd(["pactl", "set-sink-mute", "@DEFAULT_SINK@", "1" if muted else "0"])
# -------------------------------------------------

# --------- INSTRUMENT / TRACK FILTERS ---------
def _read_instrument_filters() -> dict:
    try:
        with open(INSTRUMENT_FILTERS_FILE, "r") as f:
            data = json.load(f)
            return data if isinstance(data, dict) else {}
    except Exception:
        return {}


def _write_instrument_filters(cfg: dict) -> None:
    try:
        with open(INSTRUMENT_FILTERS_FILE, "w") as f:
            json.dump(cfg, f, indent=2)
    except Exception as e:
        print(f"[WARN] Could not write instrument filters: {e}")


def _song_filter_key(path: str) -> str:
    return os.path.abspath(str(path))


def _note_name(num: int) -> str:
    names = ["C", "C#", "D", "D#", "E", "F", "F#", "G", "G#", "A", "A#", "B"]
    num = int(num)
    return f"{names[num % 12]}{(num // 12) - 1}"


def _instrument_program_name(inst) -> str:
    if getattr(inst, "is_drum", False):
        return "Drums/Percussion"
    try:
        return pretty_midi.program_to_instrument_name(int(inst.program))
    except Exception:
        return f"Program {getattr(inst, 'program', '?')}"


_PRETTY_MIDI_CACHE_LOCK = threading.RLock()
_PRETTY_MIDI_CACHE = {}
_PRETTY_MIDI_CACHE_ORDER = []
_PRETTY_MIDI_CACHE_MAX = 8


def _pretty_midi_cache_key(midi_path):
    try:
        path_abs = _safe_abs(midi_path)
        st = os.stat(path_abs)
        return (path_abs, int(getattr(st, "st_mtime_ns", int(st.st_mtime * 1_000_000_000))), int(st.st_size))
    except Exception:
        return None


def _remember_pretty_midi_cache(key, pm):
    if key is None:
        return
    try:
        with _PRETTY_MIDI_CACHE_LOCK:
            _PRETTY_MIDI_CACHE[key] = pm
            if key in _PRETTY_MIDI_CACHE_ORDER:
                _PRETTY_MIDI_CACHE_ORDER.remove(key)
            _PRETTY_MIDI_CACHE_ORDER.append(key)
            while len(_PRETTY_MIDI_CACHE_ORDER) > _PRETTY_MIDI_CACHE_MAX:
                old_key = _PRETTY_MIDI_CACHE_ORDER.pop(0)
                _PRETTY_MIDI_CACHE.pop(old_key, None)
    except Exception:
        pass


def _safe_pretty_midi(midi_path):
    """Load MIDI robustly and cache parsed PrettyMIDI objects by path/mtime/size."""
    key = _pretty_midi_cache_key(midi_path)
    if key is not None:
        try:
            with _PRETTY_MIDI_CACHE_LOCK:
                cached = _PRETTY_MIDI_CACHE.get(key)
                if cached is not None:
                    return cached
        except Exception:
            pass

    try:
        pm = pretty_midi.PrettyMIDI(midi_path)
    except Exception as exc:
        # Some internet MIDI files contain invalid data bytes (>127). mido can clip
        # those bytes while parsing, then PrettyMIDI can consume the repaired object.
        try:
            from mido import MidiFile
            mid = MidiFile(midi_path, clip=True)
            print(f"[WARN] MIDI had invalid data bytes; clipped to 0..127: {os.path.basename(str(midi_path))}")
            pm = pretty_midi.PrettyMIDI(mido_object=mid)
        except Exception as clipped_exc:
            raise RuntimeError(f"{exc}; clipped fallback also failed: {clipped_exc}") from clipped_exc

    _remember_pretty_midi_cache(key, pm)
    return pm


def _valid_midi_data_byte(value) -> bool:
    try:
        value = int(value)
        return 0 <= value <= 127
    except Exception:
        return False


def get_midi_instrument_info(midi_path: str):
    """Return display/filter metadata for each PrettyMIDI instrument."""
    pm = _safe_pretty_midi(midi_path)
    info = []
    for idx, inst in enumerate(pm.instruments):
        notes = list(getattr(inst, "notes", []))
        pitches = [int(n.pitch) for n in notes]
        if pitches:
            note_range = f"{_note_name(min(pitches))}-{_note_name(max(pitches))}"
            min_pitch = min(pitches)
            max_pitch = max(pitches)
            avg_pitch = sum(pitches) / len(pitches)
        else:
            note_range = "no notes"
            min_pitch = max_pitch = avg_pitch = 0
        name = (getattr(inst, "name", "") or "").strip()
        program_name = _instrument_program_name(inst)
        label_name = name if name else program_name
        info.append({
            "index": idx,
            "name": label_name,
            "program": int(getattr(inst, "program", 0)),
            "program_name": program_name,
            "is_drum": bool(getattr(inst, "is_drum", False)),
            "note_count": len(notes),
            "range": note_range,
            "min_pitch": min_pitch,
            "max_pitch": max_pitch,
            "avg_pitch": avg_pitch,
        })
    return info


def _default_enabled_instrument_indices(info):
    # Match the old behavior: all non-drum tracks with notes are enabled.
    enabled = [x["index"] for x in info if x.get("note_count", 0) > 0 and not x.get("is_drum", False)]
    if not enabled:
        enabled = [x["index"] for x in info if x.get("note_count", 0) > 0]
    return enabled


def get_instrument_settings_for_song(midi_path: str, info=None) -> dict:
    if info is None:
        try:
            info = get_midi_instrument_info(midi_path)
        except Exception:
            info = []
    valid = {int(x["index"]) for x in info}
    store = _read_instrument_filters()
    entry = store.get(_song_filter_key(midi_path), {})
    if not isinstance(entry, dict):
        entry = {}

    # Backward compatibility:
    #   old files used enabled_indices for piano tracks and speaker audio was the complement.
    #   new files use piano_indices and speaker_indices independently.
    if "piano_indices" in entry:
        piano = [int(i) for i in entry.get("piano_indices", []) if int(i) in valid]
    elif "enabled_indices" in entry:
        piano = [int(i) for i in entry.get("enabled_indices", []) if int(i) in valid]
    else:
        piano = _default_enabled_instrument_indices(info)

    if "speaker_indices" in entry:
        speakers = [int(i) for i in entry.get("speaker_indices", []) if int(i) in valid]
    else:
        # Keyboard recordings should be audible through FluidSynth/keyboard playback by default.
        # Normal library MIDI files keep the old complement behavior to avoid doubled piano tracks.
        if _is_keyboard_recording_path(midi_path):
            speakers = [int(x["index"]) for x in info if x.get("note_count", 0) > 0]
        else:
            piano_set = {int(i) for i in piano}
            speakers = [
                int(x["index"])
                for x in info
                if x.get("note_count", 0) > 0 and int(x["index"]) not in piano_set
            ]

    raw_scales = entry.get("piano_volume_scales", entry.get("track_volume_scales", {}))
    piano_volume_scales = _normalize_piano_volume_scales(raw_scales, info=info)

    return {
        "enabled_indices": piano,       # old name kept for existing code paths
        "piano_indices": piano,
        "speaker_indices": speakers,
        "piano_volume_scales": piano_volume_scales,
        "filter_audio": True,
        "audio_mode": entry.get("audio_mode", "custom"),
    }


def save_instrument_settings_for_song(midi_path: str, piano_indices, speaker_indices=None, filter_audio: bool = True, piano_volume_scales=None) -> None:
    if speaker_indices is None:
        try:
            info = get_midi_instrument_info(midi_path)
        except Exception:
            info = []
        piano_set = {int(i) for i in (piano_indices or [])}
        speaker_indices = [
            int(x["index"])
            for x in info
            if x.get("note_count", 0) > 0 and int(x["index"]) not in piano_set
        ]

    piano_sorted = sorted({int(i) for i in (piano_indices or [])})
    speaker_sorted = sorted({int(i) for i in (speaker_indices or [])})

    store = _read_instrument_filters()
    key = _song_filter_key(midi_path)
    entry = store.get(key, {})
    if not isinstance(entry, dict):
        entry = {}

    existing_scales = entry.get("piano_volume_scales", entry.get("track_volume_scales", {}))
    merged_scales = _normalize_piano_volume_scales(existing_scales)
    if piano_volume_scales is not None:
        merged_scales.update(_normalize_piano_volume_scales(piano_volume_scales))

    # Save with string keys because JSON insists on being JSON. How daring.
    scale_json = {str(int(k)): _clamp_percent(v, 100) for k, v in merged_scales.items()}

    entry.update({
        "piano_indices": piano_sorted,
        "speaker_indices": speaker_sorted,
        "enabled_indices": piano_sorted,  # backward compatibility with earlier patched versions
        "piano_volume_scales": scale_json,
        "filter_audio": True,
        "audio_mode": "custom",          # speakers are independently selectable now
    })

    store[key] = entry
    _write_instrument_filters(store)


def get_song_playback_settings_for_song(midi_path: str) -> dict:
    """Return saved per-song volume / strike-floor settings, if present."""
    try:
        entry = _read_instrument_filters().get(_song_filter_key(midi_path), {})
    except Exception:
        entry = {}

    if not isinstance(entry, dict):
        return {}

    result = {}

    if "master_volume" in entry:
        try:
            result["master_volume"] = max(0, min(100, int(float(entry["master_volume"]))))
        except Exception:
            pass

    if "min_strike_frac" in entry:
        try:
            result["min_strike_frac"] = max(0.0, min(1.0, float(entry["min_strike_frac"])))
        except Exception:
            pass
    elif "strike_floor_pct" in entry:
        try:
            result["min_strike_frac"] = max(0.0, min(1.0, float(entry["strike_floor_pct"]) / 100.0))
        except Exception:
            pass

    return result


def save_song_playback_settings_for_song(midi_path: str, master_volume=None, min_strike_frac=None) -> None:
    """Save per-song volume / strike-floor settings into instrument_filters.json."""
    if not midi_path:
        return

    store = _read_instrument_filters()
    key = _song_filter_key(midi_path)
    entry = store.get(key, {})
    if not isinstance(entry, dict):
        entry = {}

    if master_volume is not None:
        try:
            entry["master_volume"] = max(0, min(100, int(round(float(master_volume)))))
        except Exception:
            pass

    if min_strike_frac is not None:
        try:
            frac = max(0.0, min(1.0, float(min_strike_frac)))
            entry["min_strike_frac"] = frac
            entry["strike_floor_pct"] = int(round(frac * 100))
        except Exception:
            pass

    store[key] = entry
    _write_instrument_filters(store)


def get_audio_complement_indices_for_song(midi_path: str, enabled_indices=None, info=None):
    """Return MIDI instrument indexes that should be heard through the speakers.

    Despite the historical name, this now reads the independent speaker track
    selection saved by the two-column Instrument Mixer. If no speaker selection
    exists yet, it falls back to the old complement-of-piano behavior.
    """
    if info is None:
        try:
            info = get_midi_instrument_info(midi_path)
        except Exception:
            info = []
    settings = get_instrument_settings_for_song(midi_path, info=info)
    return [int(i) for i in settings.get("speaker_indices", [])]


def _selected_instrument_set(instrument_indices):
    if instrument_indices is None:
        return None
    return {int(i) for i in instrument_indices}


def _clamp_percent(value, default=100) -> int:
    try:
        return max(0, min(100, int(round(float(value)))))
    except Exception:
        return int(default)


def _normalize_piano_volume_scales(scales, info=None) -> dict:
    """Normalize per-instrument physical-piano volume scalers.

    Values are percentages of the main Volume slider: 100 means normal, 50 means
    half of the current main piano volume, 0 means physically silent.
    """
    if not isinstance(scales, dict):
        scales = {}

    valid = None
    if info is not None:
        try:
            valid = {int(x["index"]) for x in info}
        except Exception:
            valid = None

    result = {}

    # Preserve any saved values first.
    for key, value in scales.items():
        try:
            idx = int(key)
        except Exception:
            continue
        if valid is not None and idx not in valid:
            continue
        result[idx] = _clamp_percent(value, 100)

    # Default any known instruments to 100%.
    if valid is not None:
        for idx in valid:
            result.setdefault(int(idx), 100)

    return result
# ---------------------------------------------

# --------- SOLENOID TIMING / VOLUME ---------
STRIKE_DURATION = 0.05      # seconds
MIN_NOTE_ON_DURATION = 0.00 # seconds
MIN_REFRACTORY_OFF = float(_cfg.get("min_refractory_off", 0.075))  # minimum same-note off gap before re-strike, seconds

MASTER_VOLUME = float(_cfg.get("master_volume", 100.0))  # 0..100
MIN_VOL_FRAC = 0.55
_MASTER_VOL_FRAC = MIN_VOL_FRAC + (MASTER_VOLUME / 100.0) * (1.0 - MIN_VOL_FRAC)

# Floor for velocity-scaled *strike* power (raise if low velocities don't actuate reliably)
# Now loaded from config and adjustable live via a slider (0..1.0).
MIN_STRIKE_FRAC = float(_cfg.get("min_strike_frac", 0.85))

MIN_HOLD_FRAC = 0.63

# Per-track volume scalers need a real dynamic range.
# The global MIN_STRIKE_FRAC may be intentionally high so every solenoid actuates,
# but using that as the per-track floor makes 2% sound almost like 100%.
# These are lower nonzero floors used only by the per-track mixer. Tune in
# player_config.json if your hardware needs more/less kick.
TRACK_VOLUME_STRIKE_FLOOR_FRAC = float(_cfg.get("track_volume_strike_floor_frac", 0.25))
TRACK_VOLUME_HOLD_FLOOR_FRAC = float(_cfg.get("track_volume_hold_floor_frac", 0.10))

# Rush Mode is for black-MIDI / impossible visual files like Rush E.
# It only filters the physical solenoid/LED event stream. Audio and visualizer
# can still show/play the full selected MIDI, while the piano gets something
# vaguely compatible with motors, coils, and the tragic existence of inertia.
RUSH_MODE_MIN_NOTE_DURATION = float(_cfg.get("rush_mode_min_note_duration", 0.018))
RUSH_MODE_BIN_SECONDS = float(_cfg.get("rush_mode_bin_seconds", 0.050))
RUSH_MODE_MAX_NOTES_PER_BIN = int(_cfg.get("rush_mode_max_notes_per_bin", 8))
RUSH_MODE_MAX_SIMULTANEOUS = int(_cfg.get("rush_mode_max_simultaneous", 12))
# --------------------------------------------

# --------- KEY mapping PCA9685 (unchanged) ---------
allowed_mapping = {}
for i in range(88):
    midi_note = i + 21
    if i < 16:
        allowed_mapping[midi_note] = ("pca0", i)
    elif i < 32:
        allowed_mapping[midi_note] = ("pca1", i - 16)
    elif i < 48:
        allowed_mapping[midi_note] = ("pca2", i - 32)
    elif i < 64:
        allowed_mapping[midi_note] = ("pca3", i - 48)
    elif i < 80:
        allowed_mapping[midi_note] = ("pca4", i - 64)
    else:
        allowed_mapping[midi_note] = ("pca5", i - 80)
# ------------------------------------------------------


# ===== Sustain Pedal (MIDI CC 64) wiring & profile =====
SUSTAIN_BOARD_ID = "pca5"
SUSTAIN_CHANNEL  = 15  # <-- your wiring

# Pedal profiles are selected by the REAL_PIANO flag near the top of this file.
# Times are in milliseconds; duty fractions are 0.0..1.0.
if REAL_PIANO:
    # Real acoustic piano pedal profile.
    preload_ms      = 0    # How long the pedal solenoid gets a gentle pre-push before the real strike.
    preload_frac    = 0.00 # The power level during preload.
    strike_ms       = 120  # How long the pedal gets the hard initial push. If the pedal does not go fully down, increase this first.
    strike_frac     = 0.95 # Strike power. 1.00 means full power.
    settle_ms       = 0
    settle_frac     = 0.45
    hold_frac       = 0.75
    brake_delay_ms  = 0
    brake_ms        = 400
    brake_frac      = 0.70
    # Minimum time the pedal must be physically UP before the next press.
    # The scheduler tries to preserve the next pedal-down timing by releasing early,
    # rather than delaying the next down event and dragging the song late.
    SUSTAIN_MIN_UP_TIME = 0.01
else:
    # Keyboard test-rig pedal profile.
    preload_ms      = 0
    preload_frac    = 0.20
    strike_ms       = 40
    strike_frac     = 0.75
    settle_ms       = 0
    settle_frac     = 0.45
    hold_frac       = 0.1  # Held until pedal-up.
    brake_delay_ms  = 0
    brake_ms        = 0
    brake_frac      = 0.00
    # Minimum time the pedal must be physically UP before the next press.
    SUSTAIN_MIN_UP_TIME = 0.2

def _duty_from_frac(frac: float) -> int:
    """Convert 0.0..1.0 to 16-bit duty. Pedal ignores master volume on purpose."""
    frac = max(0.0, min(1.0, float(frac)))
    return int(frac * 0xFFFF)

# Runtime pedal state (scoped to the asyncio loop)
_pedal_task = None  # asyncio.Task managing the pedal timeline for the current song

def velocity_to_hold_duty(velocity: int, piano_volume_scale_pct: int = 100) -> int:
    """Scale hold power with a smaller nonzero floor.

    100% keeps the old normal hold behavior.
    0% mutes the track.
    Low-but-nonzero values now actually get quieter instead of all jumping
    back to the full hold duty. If a track drops out at very low values, turn
    that track up a bit. Amazing, hardware has thresholds.
    """
    scale_pct = _clamp_percent(piano_volume_scale_pct, 100)
    if scale_pct <= 0:
        return 0

    scale = scale_pct / 100.0
    normal_frac = max(velocity / 127.0, MIN_HOLD_FRAC)
    floor_frac = max(0.0, min(float(TRACK_VOLUME_HOLD_FLOOR_FRAC), normal_frac))
    frac = floor_frac + (normal_frac - floor_frac) * scale
    return int(frac * 0xFFFF * _MASTER_VOL_FRAC)

def velocity_to_strike_duty(velocity: int, piano_volume_scale_pct: int = 100) -> int:
    """Scale initial strike with a useful low-volume floor.

    The previous version preserved MIN_STRIKE_FRAC as the nonzero minimum.
    That prevented missed notes, but with MIN_STRIKE_FRAC around 0.85, a track
    at 2% was still basically an 85% strike. Helpful if your goal is no volume
    control whatsoever.

    This version keeps 100% unchanged, keeps 0% as true mute, but maps low
    nonzero track values down toward TRACK_VOLUME_STRIKE_FLOOR_FRAC instead of
    MIN_STRIKE_FRAC.
    """
    scale_pct = _clamp_percent(piano_volume_scale_pct, 100)
    if scale_pct <= 0:
        return 0

    scale = scale_pct / 100.0
    v = max(1, min(127, int(velocity)))
    normal_frac = MIN_STRIKE_FRAC + (v / 127.0) * (1.0 - MIN_STRIKE_FRAC)
    floor_frac = max(0.0, min(float(TRACK_VOLUME_STRIKE_FLOOR_FRAC), normal_frac))
    frac = floor_frac + (normal_frac - floor_frac) * scale
    return int(frac * 0xFFFF * _MASTER_VOL_FRAC)


# --------- I2C / PCA9685 SETUP (unchanged method) ---------
i2c = busio.I2C(board.SCL, board.SDA)

pca0 = PCA9685(i2c, address=0x40); pca0.frequency = 1000
pca1 = PCA9685(i2c, address=0x41); pca1.frequency = 1000
pca2 = PCA9685(i2c, address=0x42); pca2.frequency = 1000
pca3 = PCA9685(i2c, address=0x43); pca3.frequency = 1000
pca4 = PCA9685(i2c, address=0x44); pca4.frequency = 1000
pca5 = PCA9685(i2c, address=0x45); pca5.frequency = 1000

boards = {"pca0": pca0, "pca1": pca1, "pca2": pca2, "pca3": pca3, "pca4": pca4, "pca5": pca5}
# ----------------------------------------------------------

def all_off():
    for bid in boards:
        for ch in range(16):
            boards[bid].channels[ch].duty_cycle = 0

# Global state to guard solenoids while paused
SOLENOIDS_PAUSED = False

async def safe_set_duty(board_id: str, channel: int, value: int):
    for _ in range(3):
        try:
            boards[board_id].channels[channel].duty_cycle = value
            return
        except OSError:
            await asyncio.sleep(0.005)
    print(f"[WARN] I2C write failed (board {board_id}, ch {channel})")

active_notes = {}  # (board_id, channel) -> bool

def cut_all_solenoids_and_clear():
    """Cut power to all coils and mark notes inactive so pending holds won't re-energize."""
    all_off()
    for k in list(active_notes.keys()):
        active_notes[k] = False

# --------------------- LED STRIP ---------------------
# Strip: 217 LEDs over 88 keys (change to your length here)
neo = Pi5Neo('/dev/spidev0.0', 218, 1200)
active_midi_notes = set()
# note -> {track_index: active_count}; lets Track effect color the physical LED strip.
active_midi_note_track_counts = {}
_random_rgb_cache = {}


def _activate_midi_note(note, track_index=None):
    try:
        note = int(note)
    except Exception:
        return
    active_midi_notes.add(note)
    if track_index is None:
        return
    try:
        track_index = int(track_index)
    except Exception:
        return
    counts = active_midi_note_track_counts.setdefault(note, {})
    counts[track_index] = counts.get(track_index, 0) + 1


def _deactivate_midi_note(note, track_index=None):
    try:
        note = int(note)
    except Exception:
        return
    if track_index is None:
        active_midi_notes.discard(note)
        active_midi_note_track_counts.pop(note, None)
        return
    try:
        track_index = int(track_index)
    except Exception:
        active_midi_notes.discard(note)
        active_midi_note_track_counts.pop(note, None)
        return
    counts = active_midi_note_track_counts.get(note)
    if counts:
        remaining = counts.get(track_index, 0) - 1
        if remaining > 0:
            counts[track_index] = remaining
        else:
            counts.pop(track_index, None)
        if counts:
            return
    active_midi_note_track_counts.pop(note, None)
    active_midi_notes.discard(note)


def _active_track_for_midi_note(note):
    try:
        counts = active_midi_note_track_counts.get(int(note), {})
        if counts:
            # Deterministic if multiple tracks hold the same pitch.
            return sorted(counts.keys())[0]
    except Exception:
        pass
    return None


def _clear_active_midi_notes():
    active_midi_notes.clear()
    active_midi_note_track_counts.clear()
current_led_effect = _led_cfg.get("effect", "Solid")

# LED rendering is done by one worker thread. Playback events only update
# active_midi_notes and wake this worker so the strip renders immediately
# instead of waiting for the next 30/120 Hz polling tick. Tiny latency goblin, caged.
_led_render_lock = threading.Lock()
_led_render_event = threading.Event()

def _request_led_render():
    try:
        _led_render_event.set()
    except Exception:
        pass

def _hsv_to_rgb(h: float, s: float, v: float) -> Tuple[int, int, int]:
    h = float(h) % 360.0
    s = float(s); v = float(v)
    c = v * s
    x = c * (1 - abs(((h / 60.0) % 2) - 1))
    m = v - c
    if h < 60:   rp, gp, bp = c, x, 0
    elif h < 120: rp, gp, bp = x, c, 0
    elif h < 180: rp, gp, bp = 0, c, x
    elif h < 240: rp, gp, bp = 0, x, c
    elif h < 300: rp, gp, bp = x, 0, c
    else:         rp, gp, bp = c, 0, x
    return int((rp+m)*255), int((gp+m)*255), int((bp+m)*255)


def _clamp255(value) -> int:
    return max(0, min(255, int(value)))


# Track effect colors use a smooth rainbow by track number:
# lowest instrument row = red, highest = violet, evenly spaced in between.
current_track_color_count = int(_led_cfg.get("track_color_count", 16) or 16)


def _set_current_track_color_count(count) -> int:
    global current_track_color_count
    try:
        count = int(count)
    except Exception:
        count = 16
    current_track_color_count = max(1, count)
    try:
        _led_cfg["track_color_count"] = current_track_color_count
    except Exception:
        pass
    return current_track_color_count


def track_color_for_index(track_index, brightness: float = 1.0, track_count: Optional[int] = None) -> Tuple[int, int, int]:
    """Color for one MIDI instrument/track index.

    Small-track songs get simple musical colors:
      1 track  -> blue
      2 tracks -> blue, red
      3 tracks -> blue, red, green

    Larger songs keep the previous rainbow spread from red to violet.
    """
    try:
        idx = int(track_index)
    except Exception:
        idx = 0
    try:
        brightness = float(brightness)
    except Exception:
        brightness = 1.0
    brightness = max(0.0, min(1.0, brightness))

    if track_count is None:
        try:
            track_count = int(_led_cfg.get("track_color_count", current_track_color_count))
        except Exception:
            track_count = current_track_color_count
    try:
        track_count = max(1, int(track_count))
    except Exception:
        track_count = max(1, int(current_track_color_count or 16))

    idx = max(0, min(idx, track_count - 1))

    if track_count == 1:
        r, g, b = (0, 80, 255)       # blue
    elif track_count == 2:
        r, g, b = ((0, 80, 255), (255, 0, 0))[idx]  # blue, red
    elif track_count == 3:
        r, g, b = ((0, 80, 255), (255, 0, 0), (0, 255, 0))[idx]  # blue, red, green
    else:
        hue = 275.0 * (idx / float(track_count - 1))
        r, g, b = _hsv_to_rgb(hue, 1.0, brightness)
        return _clamp255(r), _clamp255(g), _clamp255(b)

    return _clamp255(r * brightness), _clamp255(g * brightness), _clamp255(b * brightness)


def _rgb_to_hex(rgb) -> str:
    try:
        r, g, b = rgb
        return f"#{_clamp255(r):02x}{_clamp255(g):02x}{_clamp255(b):02x}"
    except Exception:
        return "#ffffff"


def _stable_random_rgb_for_note(midi_note: int) -> Tuple[int, int, int]:
    """
    Deterministic "random" color per MIDI note.
    This lets the LED strip and visualizer agree without sharing live process state.
    """
    seed = (int(midi_note) * 1103515245 + 12345) & 0xFFFFFFFF
    rng = random.Random(seed)
    return rng.randint(0, 255), rng.randint(0, 255), rng.randint(0, 255)


def _stable_flicker_value(midi_note: int, t: float, speed: float) -> float:
    """
    Deterministic flicker value for a note/time bucket.
    Both the LED worker and pygame visualizer can compute the same flicker color.
    """
    rate = max(1.0, float(speed))
    bucket = int(float(t) * rate)
    seed = (int(midi_note) * 1315423911 + bucket * 2654435761) & 0xFFFFFFFF
    rng = random.Random(seed)
    return rng.uniform(0.5, 1.0)


def led_color_for_note(midi_note: int, t: Optional[float] = None, cfg: Optional[dict] = None,
                       effect: Optional[str] = None, track_index: Optional[int] = None) -> Tuple[int, int, int]:
    """
    Single source of truth for note-driven LED/visualizer colors.

    This mirrors the LED strip effects:
      Solid, RGB, Random RGB, Rainbow Effect, Moving Rainbow,
      Dancing, Flicker, Christmas.

    Random RGB and Flicker are deterministic so the separate pygame visualizer
    process can match the physical LED strip instead of inventing its own disco.
    """
    if t is None:
        t = time.time()
    if cfg is None:
        cfg = _led_cfg
    if effect is None:
        effect = cfg.get("effect", current_led_effect)

    bright = max(0, min(100, int(cfg.get("brightness", 100)))) / 100.0
    speed = cfg.get("speed", 20)

    note = int(midi_note)
    idx = note - 21  # 0..87 on an 88-key piano

    # Notes outside the 88-key piano range should not normally reach this
    # for the physical LEDs. Clamp for visualization safety rather than
    # drawing mystery colors at impossible keyboard positions.
    idx = max(0, min(87, idx))

    # default: sliders' RGB (used by Solid and unknown effects)
    r = int((int(cfg.get("red", 100)) / 100.0) * 255 * bright)
    g = int((int(cfg.get("green", 100)) / 100.0) * 255 * bright)
    b = int((int(cfg.get("blue", 100)) / 100.0) * 255 * bright)

    if effect == "Track":
        r, g, b = track_color_for_index(track_index, bright, cfg.get("track_color_count"))

    elif effect == "RGB":
        sel = idx % 3
        if sel == 0:
            r, g, b = int(255 * bright), 0, 0
        elif sel == 1:
            r, g, b = 0, int(255 * bright), 0
        else:
            r, g, b = 0, 0, int(255 * bright)

    elif effect == "Random RGB":
        r0, g0, b0 = _stable_random_rgb_for_note(note)
        r, g, b = int(r0 * bright), int(g0 * bright), int(b0 * bright)

    elif effect == "Rainbow Effect":
        hue = (idx / 88.0) * 360.0
        r, g, b = _hsv_to_rgb(hue, 1, 1)
        r, g, b = int(r * bright), int(g * bright), int(b * bright)

    elif effect == "Moving Rainbow":
        hue = (idx * 4 + float(t) * float(speed) * 5) % 360
        r, g, b = _hsv_to_rgb(hue, 1, 1)
        r, g, b = int(r * bright), int(g * bright), int(b * bright)

    elif effect == "Dancing":
        phase = (float(t) * (float(speed) / 6.0) + idx * 0.1) % 2.0
        v = 1.0 - abs(phase - 1.0)
        hue = (idx / 88.0) * 360.0
        rr, gg, bb = _hsv_to_rgb(hue, 1, v)
        r, g, b = int(rr * bright), int(gg * bright), int(bb * bright)

    elif effect == "Flicker":
        v = _stable_flicker_value(note, float(t), float(speed))
        hue = (idx / 88.0) * 360.0
        rr, gg, bb = _hsv_to_rgb(hue, 1, v)
        r, g, b = int(rr * bright), int(gg * bright), int(bb * bright)

    elif effect == "Christmas":
        if idx % 2 == 0:
            r, g, b = int(255 * bright), 0, 0
        else:
            r, g, b = 0, int(255 * bright), 0

    return _clamp255(r), _clamp255(g), _clamp255(b)

def _get_led_range(midi_note: int) -> Optional[Tuple[int,int]]:
    if midi_note < 21 or midi_note > 108:
        return None
    idx = midi_note - 21
    start = int(idx * 218 / 88)
    end   = int((idx + 1) * 218 / 88)
    return start, end

def _render_led_strip_unlocked(gui):
    bright = max(0, min(100, _led_cfg.get("brightness", 100))) / 100.0
    total_leds = 218

    # (optional but recommended) clear the frame to avoid ghost pixels
    neo.fill_strip(0, 0, 0)

    # Case 1: Song playing (note-driven LEDs)
    if active_midi_notes:
        eff = current_led_effect
        t = time.time()
        speed = _led_cfg.get("speed", 20)

        for note in list(active_midi_notes):  # snapshot to avoid concurrent modification
            rng = _get_led_range(note)
            if not rng:
                continue
            start, end = rng
            r, g, b = led_color_for_note(note, t=t, cfg=_led_cfg, effect=eff, track_index=_active_track_for_midi_note(note))

            for i in range(start, end):
                neo.set_led_color(i, r, g, b)

    # Case 2: Nothing playing -> idle pattern, unless live keyboard activity
    # has temporarily blanked idle mode. Live notes themselves are handled by
    # Case 1 above via active_midi_notes.
    elif gui.currently_playing is None and not getattr(gui, "_idle_effect_suspended", lambda: False)():
        idle_eff = _led_cfg.get("idle_effect", "Off")
        speed = _led_cfg.get("speed", 20)
        mid = total_leds / 2.0

        t = time.time()
        phase = (t * speed) % total_leds   # still used by other effects

        for i in range(total_leds):
            if idle_eff == "Off":
                r = g = b = 0
            elif idle_eff == "Solid":
                r = int((_led_cfg["red"]/100)*255*bright)
                g = int((_led_cfg["green"]/100)*255*bright)
                b = int((_led_cfg["blue"]/100)*255*bright)
            elif idle_eff == "R->L Rainbow":
                hue = ((i + phase) / total_leds) * 360 % 360
                r,g,b = _hsv_to_rgb(hue,1,1); r,g,b = int(r*bright), int(g*bright), int(b*bright)
            elif idle_eff == "L->R Rainbow":
                hue = ((i - phase) / total_leds) * 360 % 360
                r,g,b = _hsv_to_rgb(hue,1,1); r,g,b = int(r*bright), int(g*bright), int(b*bright)
            elif idle_eff == "Rainbow":
                dist = abs(i - mid)
                idx = (dist - (t*speed) % mid) % mid
                hue = (idx / mid) * 360
                r,g,b = _hsv_to_rgb(hue,1,1); r,g,b = int(r*bright), int(g*bright), int(b*bright)
            elif idle_eff == "RGB Cable":
                # Inspired by RGB PC power cables: broad scrolling color ribbons
                # with soft transitions instead of a continuous rainbow wash.
                palette = (
                    (255, 0, 0),      # red
                    (0, 255, 0),      # green
                    (0, 80, 255),     # blue
                    (255, 0, 255),    # magenta/purple
                )
                band_count = len(palette)
                cable_speed = max(1.0, min(100.0, float(speed))) * 0.85
                p = (((i + t * cable_speed) / max(1.0, float(total_leds))) * band_count) % band_count
                base = int(p)
                frac = p - base
                transition = 0.38
                if frac < (1.0 - transition):
                    mix = 0.0
                else:
                    x = (frac - (1.0 - transition)) / transition
                    mix = x * x * (3.0 - 2.0 * x)  # smoothstep
                c0 = palette[base]
                c1 = palette[(base + 1) % band_count]
                r = int((c0[0] * (1.0 - mix) + c1[0] * mix) * bright)
                g = int((c0[1] * (1.0 - mix) + c1[1] * mix) * bright)
                b = int((c0[2] * (1.0 - mix) + c1[2] * mix) * bright)
            elif idle_eff == "RGB Cable Gaps":
                # Same PC RGB cable idea, but with dark gaps between chunks
                # and reversed movement so it travels left-to-right.
                palette = (
                    (255, 0, 0),      # red
                    (0, 255, 0),      # green
                    (0, 80, 255),     # blue
                    (255, 0, 255),    # magenta/purple
                )
                band_count = len(palette)
                cable_speed = max(1.0, min(100.0, float(speed))) * 0.85
                # Opposite direction from RGB Cable.
                p = (((i - t * cable_speed) / max(1.0, float(total_leds))) * band_count) % band_count
                base = int(p)
                frac = p - base

                color_width = 0.58   # rest of each band is black space
                edge = 0.10          # soft edge so gaps aren't harsh square cuts
                if frac >= color_width:
                    r = g = b = 0
                else:
                    def _smoothstep(x):
                        x = max(0.0, min(1.0, float(x)))
                        return x * x * (3.0 - 2.0 * x)

                    intensity = 1.0
                    if frac < edge:
                        intensity = _smoothstep(frac / edge)
                    elif frac > color_width - edge:
                        intensity = _smoothstep((color_width - frac) / edge)

                    c = palette[base]
                    r = int(c[0] * bright * intensity)
                    g = int(c[1] * bright * intensity)
                    b = int(c[2] * bright * intensity)
            elif idle_eff == "4th of July":
                # Patriotic red/white/blue ribbon stripes. Moving bands keep it
                # lively without turning the strip into yet another rainbow soup.
                palette = (
                    (255, 0, 0),       # red
                    (255, 255, 255),   # white
                    (0, 80, 255),      # blue
                    (255, 255, 255),   # white separator
                )
                band_count = len(palette)
                patriotic_speed = max(1.0, min(100.0, float(speed))) * 0.75
                stripe_repeats = 2.5
                p = (((i - t * patriotic_speed) / max(1.0, float(total_leds))) * band_count * stripe_repeats) % band_count
                base = int(p)
                frac = p - base
                transition = 0.22
                if frac < (1.0 - transition):
                    mix = 0.0
                else:
                    x = (frac - (1.0 - transition)) / transition
                    mix = x * x * (3.0 - 2.0 * x)
                c0 = palette[base]
                c1 = palette[(base + 1) % band_count]
                r = int((c0[0] * (1.0 - mix) + c1[0] * mix) * bright)
                g = int((c0[1] * (1.0 - mix) + c1[1] * mix) * bright)
                b = int((c0[2] * (1.0 - mix) + c1[2] * mix) * bright)
            elif idle_eff == "Flicker":
                # Speed controls how often the random flicker pattern changes.
                # The old version generated fresh random values every LED frame,
                # so the speed slider was politely ignored like every warning label.
                flicker_rate = 0.5 + (max(1.0, min(100.0, float(speed))) / 100.0) * 24.5
                bucket = int(t * flicker_rate)
                seed = (i * 1103515245 + bucket * 2654435761) & 0xFFFFFFFF
                rng = random.Random(seed)
                v = int(255 * rng.uniform(0.35, 1.0) * bright)
                r = g = b = v
            elif idle_eff == "Christmas":
                # Big center-out red/green sections, repeating
                dist = abs(i - mid)
                scroll = (t * speed) % mid
                idx = (dist - scroll) % mid
                segment_width = mid / 3.0
                band = int(idx / segment_width)   # 0, 1, 2

                if band == 1:
                    r, g, b = 0, int(255 * bright), 0
                else:
                    r, g, b = int(255 * bright), 0, 0
            else:
                r = g = b = 0

            neo.set_led_color(i, r, g, b)

    neo.update_strip()



def _update_led_strip(gui):
    with _led_render_lock:
        _render_led_strip_unlocked(gui)


def _try_update_led_strip_now(gui):
    """Best-effort immediate LED refresh for live keyboard hits.

    The normal LED worker is fine for songs and idle effects, but for live
    key presses we want the strip to react right now. If the worker is already
    drawing, skip instead of blocking Tk and ask the worker to render next.
    """
    try:
        acquired = _led_render_lock.acquire(blocking=False)
    except TypeError:
        acquired = _led_render_lock.acquire(False)
    except Exception:
        acquired = False

    if not acquired:
        _request_led_render()
        return

    try:
        _render_led_strip_unlocked(gui)
    except Exception as e:
        print(f"[LED] fast render error: {e}")
    finally:
        try:
            _led_render_lock.release()
        except Exception:
            pass


def _clear_leds():
    with _led_render_lock:
        neo.fill_strip(0,0,0)
        neo.update_strip()

class LEDWorker(threading.Thread):
    def __init__(self, gui):
        super().__init__(daemon=True)
        self.gui = gui
        self._stop_event = threading.Event()

    def run(self):
        while not self._stop_event.is_set():
            try:
                _update_led_strip(self.gui)
            except Exception as e:
                print(f"[LED] error: {e}")

            # Adaptive fallback refresh, but wake immediately when note on/off changes.
            timeout = 1/120 if active_midi_notes else 1/30
            _led_render_event.wait(timeout)
            _led_render_event.clear()

    def stop(self):
        self._stop_event.set()
        _request_led_render()

import pathlib

class SongFolderHandler(FileSystemEventHandler):
    """Debounced refresh of the Songs list when .mid/.midi files change, and auto-fix missing extensions."""
    def __init__(self, gui):
        self.gui = gui

    def on_any_event(self, event):
        if getattr(event, "is_directory", False):
            return

        for path in [getattr(event, "src_path", ""), getattr(event, "dest_path", "")]:
            if not path:
                continue

            p = pathlib.Path(path)

            # Case 1: file already has .mid/.midi
            if p.suffix.lower() in (".mid", ".midi"):
                self.gui.schedule_watchdog_refresh()
                return

            # Case 2: file has NO extension at all
            if p.is_file() and p.suffix == "":
                new_path = p.with_suffix(".mid")
                try:
                    p.rename(new_path)
                    print(f"[INFO] Renamed {p} -> {new_path}")
                    self.gui.schedule_watchdog_refresh()
                except Exception as e:
                    print(f"[WARN] Could not rename {p}: {e}")


# -----------------------------------------------------

async def schedule_hold(board_id: str, channel: int, velocity: int, piano_volume_scale_pct: int = 100):
    await asyncio.sleep(STRIKE_DURATION)
    key = (board_id, channel)
    if active_notes.get(key, False) and not SOLENOIDS_PAUSED:
        await safe_set_duty(board_id, channel, velocity_to_hold_duty(velocity, piano_volume_scale_pct))
        
async def _pedal_activation():
    """Preload -> Strike -> Settle, back-to-back, same channel, no 'off' between."""
    if SOLENOIDS_PAUSED: 
        return
    await safe_set_duty(SUSTAIN_BOARD_ID, SUSTAIN_CHANNEL, _duty_from_frac(preload_frac))
    await asyncio.sleep(preload_ms / 1000.0)

    if SOLENOIDS_PAUSED: 
        return
    await safe_set_duty(SUSTAIN_BOARD_ID, SUSTAIN_CHANNEL, _duty_from_frac(strike_frac))
    await asyncio.sleep(strike_ms / 1000.0)

    if SOLENOIDS_PAUSED: 
        return
    await safe_set_duty(SUSTAIN_BOARD_ID, SUSTAIN_CHANNEL, _duty_from_frac(settle_frac))
    await asyncio.sleep(settle_ms / 1000.0)

async def _pedal_hold_until_up(pedal_down_flag: dict):
    """
    Hold at hold_frac until caller flips pedal_down_flag['value'] to False.
    We don't spin fast; just keep coil at the hold duty while enabled.
    """
    # Apply/maintain hold while pedal is logically down and solenoids are enabled.
    was_applied = False
    try:
        while pedal_down_flag.get("value", False):
            if not SOLENOIDS_PAUSED:
                if not was_applied:
                    await safe_set_duty(SUSTAIN_BOARD_ID, SUSTAIN_CHANNEL, _duty_from_frac(hold_frac))
                    was_applied = True
            else:
                # If paused or solenoids disabled, cut power but keep the logical 'down' state.
                if was_applied:
                    await safe_set_duty(SUSTAIN_BOARD_ID, SUSTAIN_CHANNEL, 0)
                    was_applied = False
            await asyncio.sleep(0.03)
    finally:
        # Exit leaves actual power state to the release sequence.
        pass

async def _pedal_release():
    """Off -> wait -> brake pulse -> off."""
    # Power off first
    await safe_set_duty(SUSTAIN_BOARD_ID, SUSTAIN_CHANNEL, 0)
    await asyncio.sleep(brake_delay_ms / 1000.0)

    if SOLENOIDS_PAUSED:
        # If we're paused/disabled, don't re-energize for braking.
        return
    await safe_set_duty(SUSTAIN_BOARD_ID, SUSTAIN_CHANNEL, _duty_from_frac(brake_frac))
    await asyncio.sleep(brake_ms / 1000.0)
    await safe_set_duty(SUSTAIN_BOARD_ID, SUSTAIN_CHANNEL, 0)
    
    
def _build_pedal_events(pm: pretty_midi.PrettyMIDI, start_offset: float, instrument_indices=None):
    """
    Return list of (t_rel, is_down) for sustain CC (64).
    - t_rel is seconds, relative to start_offset.
    - De-bounced to edges at threshold 64.
    - If sustain was already down at start_offset, inject a (0.0, True) event.

    instrument_indices follows the physical piano selection. If the piano column
    is empty, sustain pedal events are empty too, so the song can run as
    FluidSynth-only without thumping the pedal for no reason. Tiny mercy.
    """
    selected = _selected_instrument_set(instrument_indices)
    cc_points = []  # (time_abs, value 0..127)
    for inst_idx, inst in enumerate(pm.instruments):
        if selected is not None and inst_idx not in selected:
            continue
        if selected is None and getattr(inst, "is_drum", False):
            continue
        for cc in getattr(inst, "control_changes", []):
            if cc.number == 64:
                cc_points.append((cc.time, int(cc.value)))
    if not cc_points:
        return []

    cc_points.sort(key=lambda x: x[0])

    # State at start
    last_val = 0
    for t, v in cc_points:
        if t <= start_offset:
            last_val = v
        else:
            break
    state_down = (last_val >= 64)

    events = []
    if state_down:
        events.append((0.0, True))

    # Edges after start_offset
    prev_down = state_down
    for t, v in cc_points:
        if t < start_offset:
            continue
        down = (v >= 64)
        if down != prev_down:
            events.append((t - start_offset, down))
            prev_down = down

    # Coalesce any duplicates at the same timestamp (rare multi-track CCs)
    dedup = []
    for t, down in sorted(events, key=lambda x: x[0]):
        if not dedup or abs(t - dedup[-1][0]) > 1e-5 or down != dedup[-1][1]:
            dedup.append((t, down))
    return dedup


def _apply_sustain_min_up_time(pedal_edges, min_up_time: float):
    """Shorten pedal holds so the next pedal-down can stay on MIDI time.

    This is the sustain-pedal version of attack-priority scheduling:
      - keep pedal-down timing as close to the MIDI file as possible
      - never delay the next pedal-down just to create the up gap
      - if a release is too close to the next press, move the release earlier
      - if there is not enough room, use the best possible early release

    Returns a new [(t_rel, is_down), ...] list in playback-relative seconds.
    """
    try:
        min_up_time = max(0.0, float(min_up_time or 0.0))
    except Exception:
        min_up_time = 0.0
    if min_up_time <= 0.0 or not pedal_edges:
        return list(pedal_edges or [])

    edges = [(max(0.0, float(t)), bool(down)) for t, down in pedal_edges]
    adjusted = []
    last_down_time = None

    for idx, (t_rel, is_down) in enumerate(edges):
        if is_down:
            last_down_time = t_rel
            adjusted.append((t_rel, True))
            continue

        # Find the next pedal-down after this release.
        next_down_time = None
        for future_t, future_down in edges[idx + 1:]:
            if future_down:
                next_down_time = float(future_t)
                break

        release_t = t_rel
        if next_down_time is not None:
            latest_release_for_gap = next_down_time - min_up_time
            if release_t > latest_release_for_gap:
                release_t = latest_release_for_gap

        # Do not release before the current pedal press begins. If there is not
        # enough time for the full gap, we still prefer a shortened hold over
        # delaying the next pedal-down and making the music late.
        if last_down_time is not None:
            release_t = max(float(last_down_time), release_t)
        release_t = max(0.0, release_t)
        adjusted.append((release_t, False))

    # Keep original event order where possible. Remove impossible same-state repeats
    # after adjustment, but do not sort and accidentally move an adjusted release
    # before its matching down event. Tiny scheduling goblin, contained.
    result = []
    state = None
    for t_rel, is_down in adjusted:
        if state is not None and is_down == state:
            continue
        result.append((float(t_rel), bool(is_down)))
        state = bool(is_down)
    return result


# --------- Event builder with seeking support ---------
def build_events(pm: pretty_midi.PrettyMIDI, start_offset: float, instrument_indices=None, piano_volume_scales=None, include_inst_idx: bool = False):
    """
    Build physical solenoid/LED events from PrettyMIDI notes.

    Same-pitch protection is attack-priority:
      1. keep the new note-on at the MIDI time whenever possible;
      2. shorten the previous same-pitch note-off early to create reset time;
      3. only delay the new note-on if the previous note cannot be shortened enough;
      4. never move a note-off later than the MIDI file.

    That protects the solenoids without letting dense passages drift later and later.
    Because apparently even robots appreciate rhythm. Weirdly wholesome.
    """
    selected = _selected_instrument_set(instrument_indices)
    scale_map = _normalize_piano_volume_scales(piano_volume_scales)
    start_offset = max(0.0, float(start_offset or 0.0))

    raw_notes = []  # (ns, ne, pitch, vel, piano_volume_scale_pct, inst_idx)
    for inst_idx, inst in enumerate(pm.instruments):
        inst_idx = int(inst_idx)
        if selected is not None:
            if inst_idx not in selected:
                continue
        else:
            if inst.is_drum:
                continue

        for note in getattr(inst, "notes", []) or []:
            try:
                start_abs = float(note.start)
                end_abs = float(note.end)
                pitch = int(note.pitch)
                velocity = int(note.velocity)
            except Exception:
                continue
            if end_abs < start_offset:
                continue
            if end_abs <= start_abs:
                end_abs = start_abs + 0.03

            ns = max(start_abs, start_offset) - start_offset
            ne = end_abs - start_offset
            if ne <= ns:
                continue
            scale_pct = scale_map.get(inst_idx, 100)
            raw_notes.append((ns, ne, pitch, velocity, scale_pct, inst_idx))

    raw_notes.sort(key=lambda x: (x[0], x[2], x[5]))

    # Store mutable scheduled note records so a later same-pitch note can shorten
    # the previous note's off time without shifting the new attack.
    scheduled = []
    last_note_by_pitch = {}
    min_playable = max(0.0, float(MIN_NOTE_ON_DURATION or 0.0))
    epsilon = 0.0005

    for ns, ne, pitch, vel, scale_pct, inst_idx in raw_notes:
        ns = float(ns)
        ne = float(ne)
        pitch = int(pitch)
        inst_idx = int(inst_idx)

        prev = last_note_by_pitch.get(pitch)
        if prev is not None and ns < float(prev["off"]) + MIN_REFRACTORY_OFF:
            # First try to keep this attack exactly on time by releasing the
            # previous same-pitch note early enough for the key/solenoid to reset.
            desired_prev_off = ns - MIN_REFRACTORY_OFF
            shortest_prev_off = float(prev["on"]) + min_playable

            if desired_prev_off >= shortest_prev_off + epsilon:
                prev["off"] = min(float(prev["off"]), desired_prev_off)
            else:
                # The previous note is already too short to cut safely, so delay
                # only this note's on-time. Its off-time remains the original MIDI
                # off-time; if no playable length remains, the note is skipped.
                ns = float(prev["off"]) + MIN_REFRACTORY_OFF

        if ne <= ns + min_playable:
            continue

        board_id, channel = allowed_mapping.get(pitch, (None, None))
        rec = {
            "on": ns,
            "off": ne,
            "board_id": board_id,
            "channel": channel,
            "pitch": pitch,
            "velocity": int(vel),
            "scale_pct": scale_pct,
            "inst_idx": inst_idx,
        }
        scheduled.append(rec)
        last_note_by_pitch[pitch] = rec

    events = []
    for rec in scheduled:
        if float(rec["off"]) <= float(rec["on"]):
            continue
        on_ev = (
            float(rec["on"]), rec["board_id"], rec["channel"], True,
            int(rec["pitch"]), int(rec["velocity"]), rec["scale_pct"], int(rec["inst_idx"])
        )
        off_ev = (
            float(rec["off"]), rec["board_id"], rec["channel"], False,
            int(rec["pitch"]), None, rec["scale_pct"], int(rec["inst_idx"])
        )
        if include_inst_idx:
            events.append(on_ev)
            events.append(off_ev)
        else:
            events.append(on_ev[:-1])
            events.append(off_ev[:-1])

    events.sort(key=lambda x: (x[0], not x[3]))
    return events


# --------- Shared selected-note physical builder ---------
def _collect_selected_midi_note_items(pm: pretty_midi.PrettyMIDI, instrument_indices=None):
    """Collect selected PrettyMIDI notes once, keeping the instrument index.

    This is intentionally the same raw note source the visualizer helper uses.
    The older physical path could disagree with what the screen saw on some
    malformed/odd MIDI files. Naturally the file format invented when dinosaurs
    wore shoulder pads still finds ways to be annoying.
    """
    selected = _selected_instrument_set(instrument_indices)
    notes = []

    for inst_idx, inst in enumerate(getattr(pm, "instruments", []) or []):
        inst_idx = int(inst_idx)
        if selected is not None:
            if inst_idx not in selected:
                continue
        else:
            if getattr(inst, "is_drum", False):
                continue

        for n in getattr(inst, "notes", []) or []:
            try:
                pitch = int(n.pitch)
                velocity = int(n.velocity)
                start = float(n.start)
                end = float(n.end)
            except Exception:
                continue
            if end <= start:
                end = start + 0.03
            notes.append({
                "start": start,
                "end": end,
                "note": pitch,
                "channel": inst_idx,
                "velocity": velocity,
            })

    notes.sort(key=lambda n: (float(n.get("start", 0.0)), int(n.get("note", 0)), int(n.get("channel", 0))))
    return notes




def _rush_mode_note_priority(item) -> float:
    """Score one note for Rush Mode physical extraction.

    Higher score means more likely to survive the black-MIDI shredder. This is
    deliberately heuristic: keep longer notes, strong notes, bass anchors, and
    melody-ish material, especially Track #2 because the main melody often lives
    there while the rest of the file is trying to become weather.
    """
    try:
        start = float(item.get("start", 0.0))
        end = float(item.get("end", start + 0.03))
        dur = max(0.0, end - start)
        pitch = int(item.get("note", 60))
        velocity = int(item.get("velocity", 80))
        inst_idx = int(item.get("channel", -1))
    except Exception:
        return -9999.0

    score = 0.0
    score += dur * 260.0
    score += velocity / 12.0

    # Longer/held notes are usually the musical skeleton; tiny notes are often
    # decorative confetti in black-MIDI files.
    if dur >= 0.080:
        score += 18.0
    elif dur >= 0.040:
        score += 8.0
    elif dur < 0.016:
        score -= 40.0

    # Keep useful piano ranges. Melody tends to live up top, bass anchors below.
    if 55 <= pitch <= 96:
        score += 5.0
    if pitch >= 72:
        score += 3.0
    if pitch < 48:
        score += 4.0

    # Track #2 in the Rush E file contains important melody mixed with nonsense.
    # Keep it favored without blindly letting all 4,000+ notes through.
    if inst_idx == 1:      # GUI Track #02, because code counts from zero. Cute.
        score += 10.0
    elif inst_idx in (0, 3, 4, 5, 6):
        score += 4.0

    # Later wall/noise tracks often create the "rectangle hurricane" effect.
    if inst_idx >= 10:
        score -= 12.0

    return score


def _filter_rush_mode_note_items(note_items, start_offset: float = 0.0):
    """Return a physically-playable extraction for black-MIDI/Rush-style files.

    This does NOT change FluidSynth or the visualizer. It only thins what reaches
    the solenoid scheduler by:
      - ignoring out-of-range notes,
      - dropping ultra-short non-musical flecks,
      - limiting note starts per small time slice,
      - limiting simultaneous held solenoids.

    It is intentionally conservative enough to keep Track #2 melody material but
    aggressive enough to stop the piano from becoming a stapler convention.
    """
    try:
        start_offset = max(0.0, float(start_offset or 0.0))
    except Exception:
        start_offset = 0.0

    bin_seconds = max(0.010, float(RUSH_MODE_BIN_SECONDS))
    max_per_bin = max(1, int(RUSH_MODE_MAX_NOTES_PER_BIN))
    max_simul = max(1, int(RUSH_MODE_MAX_SIMULTANEOUS))
    min_dur = max(0.0, float(RUSH_MODE_MIN_NOTE_DURATION))

    candidates = []  # (priority, item)
    for item in note_items or []:
        try:
            pitch = int(item.get("note"))
            start = float(item.get("start", 0.0))
            end = float(item.get("end", start + 0.03))
            inst_idx = int(item.get("channel", -1))
        except Exception:
            continue

        if pitch < FIRST_NOTE or pitch > LAST_NOTE:
            continue
        if end < start_offset:
            continue
        if end <= start:
            end = start + 0.03

        dur = end - start
        # Keep Track #02 a little more generously because it carries melody in
        # the Rush E file; still drop truly microscopic dust notes.
        if dur < 0.012:
            continue
        if dur < min_dur and inst_idx != 1:
            continue

        # Work on a shallow copy so later code never sees our repair scribbles.
        fixed = dict(item)
        fixed["start"] = start
        fixed["end"] = end
        fixed["note"] = pitch
        fixed["channel"] = inst_idx
        fixed["velocity"] = int(item.get("velocity", 80) or 80)
        candidates.append((_rush_mode_note_priority(fixed), fixed))

    # Cap note starts per tiny time bucket. This preserves the best notes inside
    # dense visual clusters instead of feeding every LED rectangle to a coil.
    buckets = {}
    for priority, item in candidates:
        try:
            bucket = int(max(0.0, float(item.get("start", 0.0)) - start_offset) / bin_seconds)
        except Exception:
            bucket = 0
        buckets.setdefault(bucket, []).append((priority, item))

    bucket_kept = []
    for arr in buckets.values():
        arr.sort(key=lambda pair: (pair[0], float(pair[1].get("end", 0.0)) - float(pair[1].get("start", 0.0))), reverse=True)
        bucket_kept.extend(item for _priority, item in arr[:max_per_bin])

    # Enforce a simple simultaneous-solenoid ceiling. Earlier high-priority kept
    # notes get preference; this is intentionally not a perfect arranger, because
    # apparently we are still writing a piano robot, not hiring Liszt.
    bucket_kept.sort(key=lambda item: (float(item.get("start", 0.0)), -_rush_mode_note_priority(item)))
    active = []
    final = []
    for item in bucket_kept:
        try:
            start = float(item.get("start", 0.0))
            end = float(item.get("end", start + 0.03))
        except Exception:
            continue
        active = [held for held in active if float(held.get("end", 0.0)) > start]
        if len(active) >= max_simul:
            continue
        final.append(item)
        active.append(item)

    final.sort(key=lambda item: (float(item.get("start", 0.0)), int(item.get("note", 0)), int(item.get("channel", 0))))
    return final

def _events_from_midi_note_items(note_items, start_offset: float, piano_volume_scales=None, include_inst_idx: bool = False, rush_mode: bool = False):
    """Build solenoid/LED events from already-selected note dictionaries.

    This starts from the same selected note list as the visualizer, then applies
    attack-priority physical scheduling for the solenoids:
      - keep attacks on time when possible;
      - shorten the previous same-pitch note to create reset space;
      - delay only the new attack if shortening the previous note is impossible;
      - never move note-offs later than the MIDI file.
    """
    scale_map = _normalize_piano_volume_scales(piano_volume_scales)
    start_offset = max(0.0, float(start_offset or 0.0))

    if rush_mode:
        note_items = _filter_rush_mode_note_items(note_items, start_offset=start_offset)

    raw_notes = []  # (ns, ne, pitch, velocity, piano_volume_scale_pct, inst_idx)
    for item in note_items or []:
        try:
            start_abs = float(item.get("start", 0.0))
            end_abs = float(item.get("end", start_abs + 0.03))
            pitch = int(item.get("note"))
            velocity = int(item.get("velocity", 100))
            inst_idx = int(item.get("channel", -1))
        except Exception:
            continue

        if end_abs < start_offset:
            continue
        if end_abs <= start_abs:
            end_abs = start_abs + 0.03

        ns = max(start_abs, start_offset) - start_offset
        ne = end_abs - start_offset
        if ne <= ns:
            continue
        scale_pct = scale_map.get(inst_idx, 100)
        raw_notes.append((ns, ne, pitch, velocity, scale_pct, inst_idx))

    raw_notes.sort(key=lambda x: (x[0], x[2], x[5]))

    scheduled = []
    last_note_by_pitch = {}
    min_playable = max(0.0, float(MIN_NOTE_ON_DURATION or 0.0))
    epsilon = 0.0005

    for ns, ne, pitch, velocity, scale_pct, inst_idx in raw_notes:
        ns = float(ns)
        ne = float(ne)
        pitch = int(pitch)
        inst_idx = int(inst_idx)

        prev = last_note_by_pitch.get(pitch)
        if prev is not None and ns < float(prev["off"]) + MIN_REFRACTORY_OFF:
            desired_prev_off = ns - MIN_REFRACTORY_OFF
            shortest_prev_off = float(prev["on"]) + min_playable

            if desired_prev_off >= shortest_prev_off + epsilon:
                prev["off"] = min(float(prev["off"]), desired_prev_off)
            else:
                ns = float(prev["off"]) + MIN_REFRACTORY_OFF

        if ne <= ns + min_playable:
            continue

        board_id, channel = allowed_mapping.get(pitch, (None, None))
        rec = {
            "on": ns,
            "off": ne,
            "board_id": board_id,
            "channel": channel,
            "pitch": pitch,
            "velocity": int(velocity),
            "scale_pct": scale_pct,
            "inst_idx": inst_idx,
        }
        scheduled.append(rec)
        last_note_by_pitch[pitch] = rec

    events = []
    for rec in scheduled:
        if float(rec["off"]) <= float(rec["on"]):
            continue
        on_ev = (
            float(rec["on"]), rec["board_id"], rec["channel"], True,
            int(rec["pitch"]), int(rec["velocity"]), rec["scale_pct"], int(rec["inst_idx"])
        )
        off_ev = (
            float(rec["off"]), rec["board_id"], rec["channel"], False,
            int(rec["pitch"]), None, rec["scale_pct"], int(rec["inst_idx"])
        )
        if include_inst_idx:
            events.append(on_ev)
            events.append(off_ev)
        else:
            events.append(on_ev[:-1])
            events.append(off_ev[:-1])

    events.sort(key=lambda x: (x[0], not x[3]))
    return events


def build_events_from_selected_midi_notes(pm_or_path, start_offset: float, instrument_indices=None,
                                          piano_volume_scales=None, include_inst_idx: bool = False, rush_mode: bool = False):
    """Build physical events from the selected visualizer-style note list."""
    if isinstance(pm_or_path, pretty_midi.PrettyMIDI):
        pm = pm_or_path
    else:
        pm = _safe_pretty_midi(pm_or_path)
    notes = _collect_selected_midi_note_items(pm, instrument_indices=instrument_indices)
    return _events_from_midi_note_items(
        notes,
        start_offset,
        piano_volume_scales=piano_volume_scales,
        include_inst_idx=include_inst_idx,
        rush_mode=rush_mode,
    )
# -------------------------------------------------------

# --- Create a trimmed MIDI starting at offset (for Fluidsynth seeking) ---
def trim_midi_file_custom(original_file: str, offset: float, instrument_indices=None) -> Optional[str]:
    try:
        pm = _safe_pretty_midi(original_file)
    except Exception as e:
        print(f"[WARN] trim: failed to load {original_file}: {e}")
        return None

    selected = _selected_instrument_set(instrument_indices)
    new_pm = pretty_midi.PrettyMIDI()

    for inst_idx, inst in enumerate(pm.instruments):
        if selected is not None:
            if inst_idx not in selected:
                continue
        else:
            # For audio trimming without filtering, keep the original behavior: all instruments.
            pass

        new_inst = pretty_midi.Instrument(program=inst.program, is_drum=inst.is_drum, name=inst.name)

        for note in inst.notes:
            pitch = int(getattr(note, "pitch", -1))
            velocity = int(getattr(note, "velocity", -1))
            if not (0 <= pitch <= 127 and 0 <= velocity <= 127):
                continue
            if note.end < offset:
                continue
            ns = max(note.start, offset) - offset
            ne = note.end - offset
            if ne <= ns:
                ne = ns + 0.03
            new_inst.notes.append(pretty_midi.Note(velocity=velocity, pitch=pitch, start=ns, end=ne))

        # Preserve pitch bends / control changes after the offset when possible.
        for cc in getattr(inst, "control_changes", []):
            number = int(getattr(cc, "number", -1))
            value = int(getattr(cc, "value", -1))
            if cc.time >= offset and 0 <= number <= 127 and 0 <= value <= 127:
                new_inst.control_changes.append(pretty_midi.ControlChange(number, value, cc.time - offset))
        for pb in getattr(inst, "pitch_bends", []):
            pitch_bend = max(-8192, min(8191, int(getattr(pb, "pitch", 0))))
            if pb.time >= offset:
                new_inst.pitch_bends.append(pretty_midi.PitchBend(pitch_bend, pb.time - offset))

        if new_inst.notes or new_inst.control_changes or new_inst.pitch_bends:
            new_pm.instruments.append(new_inst)

    try:
        tmp = tempfile.NamedTemporaryFile(delete=False, suffix=".mid")
        tmp_name = tmp.name
        tmp.close()
        new_pm.write(tmp_name)
        return tmp_name
    except Exception as e:
        print(f"[WARN] trim: failed to write temp midi: {e}")
        return None

# --------- Playback with accurate pause handling ---------
class PlaybackControls:
    def __init__(self, loop):
        self.loop = loop
        self.pause_event = asyncio.Event()
        self.pause_event.set()  # not paused
        self._paused_at = None
        self.total_pause = 0.0
        self.instrument_indices = None
        self.piano_volume_scales = {}

    def pause(self):
        if self.pause_event.is_set():
            self.pause_event.clear()
            self._paused_at = self.loop.time()

    def resume(self):
        if not self.pause_event.is_set():
            paused_dur = self.loop.time() - (self._paused_at or self.loop.time())
            self.total_pause += paused_dur
            self._paused_at = None
            self.pause_event.set()

    def update_filter(self, instrument_indices=None, piano_volume_scales=None):
        """Update the physical-piano track filter without rebuilding playback events."""
        self.instrument_indices = _selected_instrument_set(instrument_indices)
        self.piano_volume_scales = _normalize_piano_volume_scales(piano_volume_scales)

    def filter_snapshot(self):
        selected = None if self.instrument_indices is None else set(self.instrument_indices)
        scales = dict(self.piano_volume_scales or {})
        return selected, scales

async def play_midi_file(path: str, start_offset: float, controls: PlaybackControls, instrument_indices=None, piano_volume_scales=None, started_callback=None, rush_mode: bool = False):
    try:
        pm = _safe_pretty_midi(path)
    except Exception as e:
        print(f"[ERROR] Failed to load MIDI: {e}")
        return

    # Build the physical event timeline from the current Piano-selected tracks,
    # using the same raw note source as the visualizer. This keeps the sync fix
    # while avoiding the missed-note behavior from the all-track PrettyMIDI path.
    try:
        controls.update_filter(instrument_indices, piano_volume_scales)
    except Exception:
        pass
    try:
        events = build_events_from_selected_midi_notes(
            pm,
            start_offset,
            instrument_indices=instrument_indices,
            piano_volume_scales=piano_volume_scales,
            include_inst_idx=True,
            rush_mode=bool(rush_mode),
        )
    except Exception as e:
        print(f"[WARN] selected-note physical builder failed; falling back to old builder: {e}")
        events = build_events(pm, start_offset, instrument_indices=instrument_indices, piano_volume_scales=piano_volume_scales, include_inst_idx=True)
    loop = asyncio.get_event_loop()
    start_arm_delay = max(0.0, float(AUDIO_SYNC_ARM_DELAY))
    t0 = loop.time() + start_arm_delay
    duration_left = max(0.0, pm.get_end_time() - start_offset)
    print(
        f"[INFO] Playing {os.path.basename(path)} from {start_offset:.2f}s | "
        f"Events={len(events)} | Remaining={duration_left:.3f}s | RushMode={'on' if rush_mode else 'off'}"
    )

    # Tell the Tk/visualizer side the exact moment the physical scheduler starts.
    # Previously the screen clock started before PrettyMIDI parsing/build_events finished,
    # so the visualizer could run nearly a second ahead of the solenoids. Cute, if
    # the goal was a player piano with a fortune-telling screen.
    if started_callback is not None:
        try:
            started_callback(float(start_offset), float(t0), time.time() + max(0.0, float(AUDIO_SYNC_ARM_DELAY)), str(path))
        except Exception as e:
            print(f"[WARN] Playback started callback failed: {e}")

    async def _wait_until_rel(t_rel: float):
        """Pause-aware wait until a relative song time has elapsed."""
        while True:
            if not controls.pause_event.is_set():
                await controls.pause_event.wait()
                continue

            target = t0 + controls.total_pause + max(0.0, float(t_rel))
            now = loop.time()
            remaining = target - now
            if remaining <= 0:
                break
            await asyncio.sleep(min(0.01, remaining))

    # ==== Sustain pedal companion task (MIDI CC 64) ====
    pedal_edges = _build_pedal_events(pm, start_offset, instrument_indices=instrument_indices)  # [(t_rel, is_down), ...]
    pedal_edges = _apply_sustain_min_up_time(pedal_edges, SUSTAIN_MIN_UP_TIME)
    pedal_state = {"value": False}  # shared flag for the hold loop
    hold_task = None
    pedal_task = None

    async def _run_pedal_track():
        nonlocal hold_task

        last_effective_rel = 0.0

        for t_rel, is_down in pedal_edges:
            # Edges have already been adjusted so the pedal gets its minimum up
            # time by releasing early where possible, not by delaying the next
            # pedal-down and making the song drag behind the MIDI.
            effective_t_rel = max(float(t_rel), last_effective_rel)
            last_effective_rel = effective_t_rel

            # Pause-aware wait until this pedal edge should occur
            while True:
                if not controls.pause_event.is_set():
                    await controls.pause_event.wait()
                    continue

                target = t0 + controls.total_pause + effective_t_rel
                now = loop.time()
                remaining = target - now
                if remaining <= 0:
                    break
                await asyncio.sleep(min(0.01, remaining))

            # Apply the pedal action
            if is_down:
                pedal_state["value"] = True
                await _pedal_activation()

                if hold_task is None or hold_task.done():
                    hold_task = asyncio.create_task(_pedal_hold_until_up(pedal_state))
            else:
                pedal_state["value"] = False

                if hold_task:
                    try:
                        await hold_task
                    except asyncio.CancelledError:
                        raise  # don't swallow cancellation
                    finally:
                        hold_task = None

                await _pedal_release()

        # No extra release here.
        # Playback teardown will cancel tasks and do the one-and-only final release.

    pedal_task = asyncio.create_task(_run_pedal_track())
    # ===================================================

    try:
        for ev in events:
            ev_time, board_id, channel, is_on, pitch, vel, _built_scale_pct, inst_idx = ev
            try:
                ev_time = float(ev_time)
            except Exception:
                ev_time = 0.0

            # Pause-aware wait for this note event. Refractory protection already
            # keeps note-off times anchored to the MIDI file, so do not skip or
            # clip late events here; that caused dropped/glitchy notes in dense songs.
            await _wait_until_rel(ev_time)

            selected_now, scales_now = controls.filter_snapshot()
            if selected_now is not None and int(inst_idx) not in selected_now:
                continue
            piano_volume_scale_pct = _clamp_percent(scales_now.get(int(inst_idx), 100), 100)

            if board_id is None:
                if is_on:
                    _activate_midi_note(pitch, inst_idx)
                else:
                    _deactivate_midi_note(pitch, inst_idx)
                _request_led_render()
                continue

            key = (board_id, channel)
            if is_on:
                # Update LED state first and wake the LED worker immediately.
                # The worker owns Pi5Neo writes, so we get low latency without two
                # threads fighting over the SPI strip like tiny raccoons over garbage.
                _activate_midi_note(pitch, inst_idx)
                _request_led_render()
                if not SOLENOIDS_PAUSED:
                    active_notes[key] = True
                    strike = velocity_to_strike_duty(vel, piano_volume_scale_pct)
                    await safe_set_duty(board_id, channel, strike)
                    asyncio.create_task(schedule_hold(board_id, channel, vel, piano_volume_scale_pct))
            else:
                was_active = bool(active_notes.get(key, False))
                active_notes[key] = False
                _deactivate_midi_note(pitch, inst_idx)
                _request_led_render()
                if was_active and not SOLENOIDS_PAUSED:
                    await safe_set_duty(board_id, channel, 0)

        # Do not let a song end just because the physical-piano track list is empty
        # or because the selected piano tracks end early. FluidSynth may still be
        # playing speaker-only accompaniment, and the scrubber/queue should honor
        # the full MIDI duration. Revolutionary concept: silence can still be time.
        await _wait_until_rel(duration_left)

    finally:
        # Teardown: stop pedal logic FIRST (so it can't keep tapping), then release once.
        try:
            pedal_state["value"] = False

            if pedal_task and not pedal_task.done():
                pedal_task.cancel()
            if pedal_task:
                try:
                    await pedal_task
                except asyncio.CancelledError:
                    pass

            if hold_task:
                # If it didn't exit quickly, force it to stop.
                if not hold_task.done():
                    hold_task.cancel()
                try:
                    await hold_task
                except asyncio.CancelledError:
                    pass
                hold_task = None

            await _pedal_release()  # single final release
        except Exception:
            pass

        all_off()
        _clear_active_midi_notes()
        _clear_leds()


# --------- PlaybackThread: asyncio loop off the Tk thread ---------
class PlaybackThread(threading.Thread):
    def __init__(self):
        super().__init__(daemon=True)
        self.loop = asyncio.new_event_loop()
        self.current_future = None
        self.controls = None

    def run(self):
        asyncio.set_event_loop(self.loop        )
        self.loop.run_forever()

    def _attach_done_callback(self, fut, done_callback):
        def _cb(f):
            try:
                f.result()

            # Cancel is normal for Stop/Seek. Don't treat it like a crash.
            except (asyncio.CancelledError, concurrent.futures.CancelledError):
                return

            except Exception as e:
                print(f"[ERROR] Playback crashed: {e!r}")
                # optionally add traceback here

            # Whether it ended cleanly or crashed, advance the queue
            done_callback()

        fut.add_done_callback(_cb)

    def play_file(self, path: str, start_offset: float, done_callback, instrument_indices=None, piano_volume_scales=None, started_callback=None, rush_mode: bool = False):
        self.stop_current()
        self.controls = PlaybackControls(self.loop)
        coro = play_midi_file(
            path,
            start_offset,
            self.controls,
            instrument_indices=instrument_indices,
            piano_volume_scales=piano_volume_scales,
            started_callback=started_callback,
            rush_mode=bool(rush_mode),
        )
        self.current_future = asyncio.run_coroutine_threadsafe(coro, self.loop)
        self._attach_done_callback(self.current_future, done_callback)

    def seek(self, path: str, start_offset: float, done_callback, instrument_indices=None, piano_volume_scales=None, started_callback=None, rush_mode: bool = False):
        self.play_file(
            path,
            start_offset,
            done_callback,
            instrument_indices=instrument_indices,
            piano_volume_scales=piano_volume_scales,
            started_callback=started_callback,
            rush_mode=bool(rush_mode),
        )

    def pause(self):
        if self.controls:
            self.loop.call_soon_threadsafe(self.controls.pause)

    def resume(self):
        if self.controls:
            self.loop.call_soon_threadsafe(self.controls.resume)

    def is_paused(self):
        return self.controls and not self.controls.pause_event.is_set()

    def update_filter(self, instrument_indices=None, piano_volume_scales=None):
        if self.controls:
            self.loop.call_soon_threadsafe(self.controls.update_filter, instrument_indices, piano_volume_scales)

    def stop_current(self):
        if self.current_future and not self.current_future.done():
            self.current_future.cancel()
        self.current_future = None
        self.controls = None
        all_off()

    def stop(self):
        try:
            self.stop_current()
            self.loop.call_soon_threadsafe(self.loop.stop)
        except Exception:
            pass

# ---------------------------- Tk GUI ---------------------------------

# -------------------- Visualizer (Pygame Falling Notes) --------------------
# Show the full MIDI note range so high melody notes never fall outside the visualizer.
# Standard 88-key piano is 21..108, but some MIDI files put melody/ornaments above that.
VISUALIZER_MIN_NOTE = 21
VISUALIZER_MAX_NOTE = 108

# --------------------------- MIDI parsing for visualizer ---------------------------

def parse_midi_notes(midi_path: str, instrument_indices=None):
    """
    Return visualizer notes at the MIDI file's original timing.

    The screen and FluidSynth live in synth/visual fantasy land; they should not
    inherit the physical solenoid refractory delay. The solenoid event builder
    still uses the same selected-note source, but only the physical path shortens
    impossible repeated notes.
    """
    pm = _safe_pretty_midi(midi_path)
    selected = _selected_instrument_set(instrument_indices)

    try:
        bpm_guess = float(pm.estimate_tempo())
        if not bpm_guess or bpm_guess <= 0:
            bpm_guess = 120.0
    except Exception:
        bpm_guess = 120.0

    notes = []
    for item in _collect_selected_midi_note_items(pm, instrument_indices=selected):
        try:
            pitch = int(item.get("note"))
            if pitch < VISUALIZER_MIN_NOTE or pitch > VISUALIZER_MAX_NOTE:
                continue
            start = max(0.0, float(item.get("start", 0.0)))
            end = float(item.get("end", start + 0.03))
            if end <= start:
                end = start + 0.03
            notes.append({
                "start": start,
                "end": end,
                "note": pitch,
                "channel": int(item.get("channel", 0)),
                "velocity": int(item.get("velocity", 80)),
            })
        except Exception:
            continue

    duration = float(pm.get_end_time())
    notes.sort(key=lambda n: n["start"])
    return notes, duration, bpm_guess

def hsv_to_rgb(h, s, v):
    i = int(h * 6.0)
    f = (h * 6.0) - i
    p = v * (1.0 - s)
    q = v * (1.0 - f * s)
    t = v * (1.0 - (1.0 - f) * s)
    i = i % 6
    if i == 0:
        r, g, b = v, t, p
    elif i == 1:
        r, g, b = q, v, p
    elif i == 2:
        r, g, b = p, v, t
    elif i == 3:
        r, g, b = p, q, v
    elif i == 4:
        r, g, b = t, p, v
    else:
        r, g, b = v, p, q
    return int(r * 255), int(g * 255), int(b * 255)



# --------------------------- Window placement helpers ---------------------------

def _get_screen_size(default=(1920, 1080)):
    """Best-effort screen size lookup for placing the pygame visualizer window."""
    try:
        import tkinter as _tk
        root = _tk.Tk()
        root.withdraw()
        w = int(root.winfo_screenwidth())
        h = int(root.winfo_screenheight())
        root.destroy()
        return w, h
    except Exception:
        return default


def _visualizer_top_right_position(w, h):
    """Return a top-right-ish window position. Keeps room for the Pi top panel when present."""
    screen_w, screen_h = _get_screen_size()
    x = max(0, screen_w - int(w))
    y = 30 if screen_h >= (int(h) + 60) else 0
    return x, y


def _compute_app_window_layout(tk_widget=None):
    """Compute non-overlapping geometry for the three app windows.

    Layout:
      - Player: top-left
      - Instrument Mixer: top-right
      - MIDI Visualizer: full-width bottom band

    Tk/SDL geometry sizes are client-area sizes, while the window manager adds
    title bars/borders outside those sizes. This function budgets for those
    decorations up front so the active window banner does not cover another
    window's bottom edge. Apparently rectangle math needs a chaperone.
    """
    try:
        if tk_widget is not None:
            screen_w = int(tk_widget.winfo_screenwidth())
            screen_h = int(tk_widget.winfo_screenheight())
        else:
            screen_w, screen_h = _get_screen_size(default=(1920, 1200))
            screen_w = int(screen_w)
            screen_h = int(screen_h)
    except Exception:
        screen_w, screen_h = 1920, 1200

    # These are deliberately conservative for WayVNC / Openbox-style title bars.
    # If the desktop theme changes, only these numbers should need tuning.
    top_panel_guard = 34 if screen_h >= 700 else 0       # Raspberry Pi top panel/taskbar area
    titlebar_guard = 34 if screen_h >= 700 else 24       # window title bar + borders
    window_gap = 30 if screen_h >= 700 else 14           # visible gap between top row and visualizer title bar
    bottom_guard = 0                                     # let the visualizer reach the bottom edge

    top_y = top_panel_guard
    available_outer_h = max(320, screen_h - top_y - bottom_guard)

    # Choose the TOP WINDOW CLIENT height. The outer height will be this plus
    # titlebar_guard. 500px is enough for the Idle Speed row without eating the
    # whole visualizer on a 1080p display. Taller screens get a little extra room.
    if available_outer_h >= 1120:
        top_client_h = 540
    elif available_outer_h >= 980:
        top_client_h = 500
    else:
        top_client_h = max(420, int(available_outer_h * 0.48) - titlebar_guard)

    # Never let the top row consume so much outer height that the visualizer becomes useless.
    max_top_client_h = max(360, available_outer_h - window_gap - titlebar_guard - 260 - titlebar_guard)
    top_client_h = min(top_client_h, max_top_client_h)
    top_client_h = max(360, top_client_h)

    top_outer_h = top_client_h + titlebar_guard
    viz_y = top_y + top_outer_h + window_gap

    # SDL/Pygame uses the requested height as the drawable client area on this setup.
    # The previous version subtracted titlebar_guard here and left a strip of desktop
    # showing at the bottom. So: protect the top boundary, but let the visualizer
    # claim the full remaining bottom band. Window managers, naturally, made this weird.
    viz_outer_h = max(160, screen_h - viz_y - bottom_guard)
    viz_client_h = max(120, viz_outer_h)

    # Final safety clamp: if a small screen forces an overlap, shrink the top client
    # before letting the visualizer run off the bottom of the display.
    if viz_y + viz_client_h + titlebar_guard > screen_h - bottom_guard:
        overflow = (viz_y + viz_client_h + titlebar_guard) - (screen_h - bottom_guard)
        if overflow > 0 and top_client_h > 360:
            shrink = min(overflow, top_client_h - 360)
            top_client_h -= shrink
            top_outer_h = top_client_h + titlebar_guard
            viz_y = top_y + top_outer_h + window_gap
            viz_outer_h = max(160, screen_h - viz_y - bottom_guard)
            viz_client_h = max(120, viz_outer_h)

    # Split the top row into player + mixer without horizontal overlap.
    if screen_w >= 1500:
        player_w = screen_w // 2
    else:
        player_w = max(640, min(960, int(screen_w * 0.52)))
    player_w = min(player_w, max(1, screen_w - 420)) if screen_w > 900 else screen_w
    mixer_x = min(screen_w, player_w)
    mixer_w = max(1, screen_w - mixer_x)

    return {
        "screen_w": screen_w,
        "screen_h": screen_h,
        "top_y": int(top_y),
        "top_h": int(top_client_h),
        "titlebar_guard": int(titlebar_guard),
        "player_x": 0,
        "player_w": int(player_w),
        "mixer_x": int(mixer_x),
        "mixer_w": int(mixer_w),
        "viz_x": 0,
        "viz_y": int(viz_y),
        "viz_w": int(screen_w),
        "viz_h": int(viz_client_h),
    }

# --------------------------- Visualizer backends ---------------------------

class _Backend:
    def __init__(self, w, h):
        self.w = w
        self.h = h

    def size(self):
        return self.w, self.h

    def clear(self, color):
        raise NotImplementedError

    def fill_rect(self, x, y, w, h, color):
        raise NotImplementedError

    def present(self):
        raise NotImplementedError

    def set_blend(self, enabled: bool):
        # default: no-op
        pass

    def shutdown(self):
        pass


class PygameSurfaceBackend(_Backend):
    def __init__(self, w, h):
        import pygame
        super().__init__(w, h)
        self.pygame = pygame
        flags = pygame.RESIZABLE | pygame.DOUBLEBUF
        self.screen = pygame.display.set_mode((w, h), flags)
        self.clock = pygame.time.Clock()

    def clear(self, color):
        self.screen.fill(color)

    def fill_rect(self, x, y, w, h, color):
        self.pygame.draw.rect(self.screen, color, self.pygame.Rect(int(x), int(y), int(w), int(h)))

    def present(self):
        self.pygame.display.flip()
        self.clock.tick(60)

    def shutdown(self):
        self.pygame.quit()


class SDL2RendererBackend(_Backend):
    def __init__(self, w, h):
        import pygame
        from pygame._sdl2.video import Window, Renderer
        super().__init__(w, h)
        self.pygame = pygame
        self.window = Window("MIDI Visualizer", size=(w, h), flags=pygame.RESIZABLE)
        self.renderer = Renderer(self.window, accelerated=True, vsync=True)
        self.clock = pygame.time.Clock()
        self._blend_enabled = None

    def set_blend(self, enabled: bool):
        import pygame
        if self._blend_enabled == enabled:
            return
        self._blend_enabled = enabled

        mode = pygame.BLENDMODE_BLEND if enabled else pygame.BLENDMODE_NONE

        # pygame builds disagree on API names
        for attr in ("blendmode", "blend_mode", "draw_blend_mode"):
            try:
                setattr(self.renderer, attr, mode)
                return
            except Exception:
                pass
        try:
            self.renderer.set_blend_mode(mode)
        except Exception:
            pass

    def clear(self, color):
        self.renderer.draw_color = (*color[:3], 255)
        self.renderer.clear()

    def fill_rect(self, x, y, w, h, color):
        import pygame
        self.renderer.draw_color = color
        self.renderer.fill_rect(pygame.Rect(int(x), int(y), int(w), int(h)))

    def present(self):
        self.renderer.present()
        self.clock.tick(60)

    def shutdown(self):
        self.pygame.quit()


# --------------------------- Visualizer (separate process) ---------------------------

def run_visualizer(midi_path: str, playback_start_mono: float, stop_event, instrument_indices=None):
    # Full-width visualizer in the computed bottom band.
    # SDL reads this before creating the window. Window managers may still override it,
    # because window managers apparently enjoy creative disagreement.
    layout = _compute_app_window_layout(None)
    W = layout["viz_w"]
    H = layout["viz_h"]
    viz_x, viz_y = layout["viz_x"], layout["viz_y"]
    os.environ["SDL_VIDEO_WINDOW_POS"] = f"{viz_x},{viz_y}"

    import pygame
    pygame.init()

    try:
        import pygame._sdl2.video  # noqa
        backend = SDL2RendererBackend(W, H)
    except Exception:
        backend = PygameSurfaceBackend(W, H)

    # Best effort for SDL2 backend after creation too.
    try:
        if hasattr(backend, "window"):
            backend.window.position = (viz_x, viz_y)
    except Exception:
        pass

    notes, duration, bpm = parse_midi_notes(midi_path, instrument_indices=instrument_indices)
    if not notes:
        t0 = time.monotonic()
        while (time.monotonic() - t0) < 2.0:
            for ev in pygame.event.get():
                if ev.type == pygame.QUIT:
                    backend.shutdown()
                    return
            backend.clear((8, 8, 14))
            backend.present()
        backend.shutdown()
        return

    starts = [n["start"] for n in notes]

    # Use a fixed full-MIDI pitch range so notes above the physical piano/solenoid
    # range still show up instead of landing outside the drawing area.
    min_note = VISUALIZER_MIN_NOTE
    max_note = VISUALIZER_MAX_NOTE
    span = max(1, (max_note - min_note))

    # Visual tuning (same look)
    lead = 2.6
    hit_y_frac = 0.86
    min_bar_h = 6
    base_bg = (8, 8, 14)

    # The visualizer uses the same LED color function as the physical strip.
    viz_led_cfg = _read_led_config()
    viz_led_cfg_last_load = 0.0

    def get_viz_led_cfg(now_wall: float):
        nonlocal viz_led_cfg, viz_led_cfg_last_load
        if now_wall - viz_led_cfg_last_load >= 0.25:
            viz_led_cfg = _read_led_config()
            viz_led_cfg_last_load = now_wall
        return viz_led_cfg

    # Stars
    star_count = 140
    stars = [{
        "x": random.random(),
        "y": random.random(),
        "spd": 0.12 + random.random() * 0.95,
        "sz": 1 + int(random.random() * 2),
    } for _ in range(star_count)]

    # Particles in tight lists:
    # [x, y, vx, vy, life, maxlife, r, g, b]
    particles = []
    MAX_PARTICLES = 9000

    # Active notes
    start_cursor = 0
    active_notes = []

    fade = 0.0
    last_now = None
    running = True

    # Cache note -> (x, bw) per window width
    cached_w = None
    xw_cache = {}

    def is_black_key(midi_note):
        return int(midi_note) % 12 in (1, 3, 6, 8, 10)

    def _active_note_numbers(note_items):
        active = set()
        for item in note_items or []:
            try:
                if isinstance(item, dict):
                    active.add(int(item.get("note")))
                else:
                    active.add(int(item))
            except Exception:
                pass
        return active

    def _active_note_track_map(note_items):
        mapping = {}
        for item in note_items or []:
            try:
                if isinstance(item, dict):
                    mapping[int(item.get("note"))] = int(item.get("channel", 0))
            except Exception:
                pass
        return mapping

    def rebuild_x_cache(screen_w):
        """Map notes to a real 88-key piano layout instead of equal semitone spacing."""
        white_count = 52
        white_w = max(1.0, float(screen_w) / white_count)
        black_w = max(4.0, white_w * 0.62)
        xw_cache.clear()

        white_index = 0
        for p in range(min_note, max_note + 1):
            if not is_black_key(p):
                x = int(white_index * white_w + white_w * 0.12)
                bar_w = int(max(4, white_w * 0.76))
                xw_cache[p] = (x, bar_w)
                white_index += 1

        white_index = 0
        for p in range(min_note, max_note + 1):
            if is_black_key(p):
                x = int(white_index * white_w - black_w * 0.5)
                bar_w = int(max(4, black_w * 0.82))
                xw_cache[p] = (x, bar_w)
            else:
                white_index += 1

    def draw_piano_keyboard(screen_w, screen_h, key_top, note_items, cfg, effect, now_wall):
        """Draw an 88-key keyboard below the hit line, with active keys colored."""
        key_top = int(min(max(0, key_top), max(0, screen_h - 8)))
        key_bottom = int(max(key_top + 8, screen_h - 4))
        key_h = max(8, key_bottom - key_top)
        white_count = 52
        white_w = max(1.0, float(screen_w) / white_count)
        black_w = max(4.0, white_w * 0.62)
        black_h = max(8, int(key_h * 0.62))
        active = _active_note_numbers(note_items)
        active_track_by_note = _active_note_track_map(note_items)

        # White keys first.
        white_index = 0
        for p in range(min_note, max_note + 1):
            if is_black_key(p):
                continue
            x = int(white_index * white_w)
            w_key = int(max(1, math.ceil((white_index + 1) * white_w) - x))
            if p in active:
                r, g, b = led_color_for_note(p, t=now_wall, cfg=cfg, effect=effect, track_index=active_track_by_note.get(p))
                color = (min(255, r + 45), min(255, g + 45), min(255, b + 45), 255)
            else:
                color = (232, 232, 224, 255)
            backend.fill_rect(x, key_top, w_key, key_h, color)
            backend.fill_rect(x, key_top, 1, key_h, (30, 32, 42, 255))
            white_index += 1
        backend.fill_rect(0, key_bottom - 2, screen_w, 2, (35, 38, 48, 255))

        # Black keys on top.
        white_index = 0
        for p in range(min_note, max_note + 1):
            if is_black_key(p):
                x = int(white_index * white_w - black_w * 0.5)
                if p in active:
                    r, g, b = led_color_for_note(p, t=now_wall, cfg=cfg, effect=effect, track_index=active_track_by_note.get(p))
                    color = (min(255, r + 25), min(255, g + 25), min(255, b + 25), 255)
                else:
                    color = (8, 8, 12, 255)
                backend.fill_rect(x, key_top, int(black_w), black_h, color)
                backend.fill_rect(x, key_top, 1, black_h, (0, 0, 0, 255))
                backend.fill_rect(x + int(black_w) - 1, key_top, 1, black_h, (0, 0, 0, 255))
            else:
                white_index += 1

    while running:
        now = max(0.0, time.monotonic() - playback_start_mono)
        wall_now = time.time()
        viz_led_cfg = get_viz_led_cfg(wall_now)
        viz_led_effect = viz_led_cfg.get("effect", "Solid")
        if last_now is None:
            dt = 1 / 60.0
        else:
            dt = max(1e-4, min(0.05, now - last_now))
        last_now = now

        if stop_event.is_set():
            fade = min(1.0, fade + dt * 2.2)

        for ev in pygame.event.get():
            if ev.type == pygame.QUIT:
                running = False
            elif ev.type in (pygame.VIDEORESIZE, getattr(pygame, "WINDOWRESIZED", pygame.VIDEORESIZE)):
                try:
                    backend.w, backend.h = ev.w, ev.h
                except Exception:
                    pass

        w, h = backend.size()
        hit_y = int(h * hit_y_frac)

        if cached_w != w:
            cached_w = w
            rebuild_x_cache(w)

        # ---------------- OPAQUE PASS ----------------
        backend.set_blend(False)
        backend.clear(base_bg)

        # Stars
        for s in stars:
            s["y"] += s["spd"] * dt * 0.33
            if s["y"] > 1.0:
                s["y"] -= 1.0
                s["x"] = random.random()
                s["spd"] = 0.12 + random.random() * 0.95
                s["sz"] = 1 + int(random.random() * 2)
            backend.fill_rect(int(s["x"] * w), int(s["y"] * h), s["sz"], s["sz"], (55, 65, 92, 255))

        # Octave grid lines
        for n in range((min_note // 12) * 12, max_note + 12, 12):
            if n < min_note or n > max_note:
                continue
            x, _bw = xw_cache.get(n, (0, 10))
            backend.fill_rect(x, 0, 2, hit_y, (14, 14, 24, 255))

        # Beat lines + hit line pulse
        beat_period = 60.0 / max(1.0, bpm)
        beat_phase = (now % beat_period) / beat_period
        # Keep the beat grid continuous by wrapping each line instead of letting
        # all six drift off-screen and then respawn like synchronized ghosts.
        grid_spacing = max(1.0, hit_y / 6.0)
        grid_offset = beat_phase * grid_spacing
        for k in range(7):
            y = int((grid_offset + k * grid_spacing) % max(1, hit_y))
            backend.fill_rect(0, y, w, 2, (16, 16, 26, 255))

        pulse = 0.4 + 0.6 * (1.0 - abs(beat_phase - 0.5) * 2.0)
        glow = int(90 * pulse)
        backend.fill_rect(0, hit_y - 12, w, 12, (10, 55 + glow // 2, min(255, 150 + glow), 255))
        backend.fill_rect(0, hit_y, w, 4, (0, 145, 255, 255))

        # Activate notes
        while start_cursor < len(notes) and notes[start_cursor]["start"] <= now:
            n = notes[start_cursor]
            active_notes.append(n)

            x, bw = xw_cache.get(n["note"], (0, 10))
            cx = x + bw * 0.5
            r, g, b = led_color_for_note(n["note"], t=wall_now, cfg=viz_led_cfg, effect=viz_led_effect, track_index=n.get("channel"))

            for _ in range(10):
                ang = random.random() * math.tau
                spd = 120 + random.random() * 260
                particles.append([
                    cx, hit_y,
                    math.cos(ang) * spd,
                    -abs(math.sin(ang) * spd) * (0.7 + random.random() * 0.6),
                    0.0,
                    0.22 + random.random() * 0.28,
                    r, g, b
                ])

            start_cursor += 1

        if active_notes:
            active_notes = [n for n in active_notes if n["end"] > now]

        # Upcoming notes
        i0 = bisect_right(starts, now)
        i1 = bisect_right(starts, now + lead)

        for n in notes[i0:i1]:
            start = n["start"]
            end = n["end"]
            dur = max(0.02, end - start)

            head_y = hit_y - ((start - now) / lead) * hit_y
            bar_h = max(min_bar_h, int((dur / lead) * hit_y))
            top_y = int(head_y - bar_h)
            bottom_y = int(head_y)

            if bottom_y < 0 or top_y > hit_y + 40:
                continue

            x, bw = xw_cache.get(n["note"], (0, 10))
            r, g, b = led_color_for_note(n["note"], t=wall_now, cfg=viz_led_cfg, effect=viz_led_effect, track_index=n.get("channel"))

            near = max(0.0, 1.0 - abs(head_y - hit_y) / 180.0)
            rr = min(255, int(r + near * 55))
            gg = min(255, int(g + near * 55))
            bb = min(255, int(b + near * 55))

            backend.fill_rect(x, top_y, bw, max(2, bottom_y - top_y), (rr, gg, bb, 255))

        # Active notes locked at hit line
        for n in active_notes:
            remaining = max(0.0, n["end"] - now)
            if remaining <= 0:
                continue

            bar_h = max(min_bar_h, int((remaining / lead) * hit_y))
            top_y = int(hit_y - bar_h)

            x, bw = xw_cache.get(n["note"], (0, 10))
            r, g, b = led_color_for_note(n["note"], t=wall_now, cfg=viz_led_cfg, effect=viz_led_effect, track_index=n.get("channel"))

            backend.fill_rect(x, top_y, bw, max(2, hit_y - top_y),
                              (min(255, r + 45), min(255, g + 45), min(255, b + 45), 255))

            vel = int(n.get("velocity", 80))
            sparks = 1 if vel < 50 else 2
            if random.random() < 0.85:
                for _ in range(sparks):
                    particles.append([
                        x + bw * (0.2 + random.random() * 0.6),
                        hit_y - random.random() * 6,
                        (random.random() - 0.5) * 120,
                        -120 - random.random() * 200,
                        0.0,
                        0.12 + random.random() * 0.18,
                        min(255, r + 70), min(255, g + 70), min(255, b + 70)
                    ])

        draw_piano_keyboard(w, h, hit_y + 6, active_notes, viz_led_cfg, viz_led_effect, wall_now)

        if len(particles) > MAX_PARTICLES:
            particles = particles[-MAX_PARTICLES:]

        # ---------------- BLENDED PASS (particles + fade) ----------------
        backend.set_blend(True)

        write_i = 0
        for i in range(len(particles)):
            p = particles[i]
            p[4] += dt
            if p[4] >= p[5]:
                continue

            p[0] += p[2] * dt
            p[1] += p[3] * dt
            p[3] += 900 * dt

            t = p[4] / p[5]
            alpha = int(255 * (1.0 - t))
            backend.fill_rect(p[0], p[1], 3, 3, (p[6], p[7], p[8], alpha))

            particles[write_i] = p
            write_i += 1

        if write_i != len(particles):
            del particles[write_i:]

        if fade > 0.0:
            a = int(255 * fade)
            backend.fill_rect(0, 0, w, h, (0, 0, 0, a))
            if fade >= 1.0:
                running = False

        backend.present()

    backend.shutdown()


_VISUALIZER_HELPER_CODE = '#!/usr/bin/env python3\nimport json\nimport math\nimport os\nimport random\nimport sys\nimport time\nimport struct\nfrom multiprocessing import shared_memory\nfrom bisect import bisect_right\n\nimport pretty_midi\n\n\ndef _safe_pretty_midi(midi_path):\n    try:\n        return pretty_midi.PrettyMIDI(midi_path)\n    except Exception as exc:\n        try:\n            from mido import MidiFile\n            mid = MidiFile(midi_path, clip=True)\n            print(f"[WARN] MIDI had invalid data bytes; clipped to 0..127: {os.path.basename(str(midi_path))}", file=sys.stderr)\n            return pretty_midi.PrettyMIDI(mido_object=mid)\n        except Exception as clipped_exc:\n            raise RuntimeError(f"{exc}; clipped fallback also failed: {clipped_exc}") from clipped_exc\n\n\nVISUALIZER_MIN_NOTE = 21\nVISUALIZER_MAX_NOTE = 108\n\n\ndef _hsv_to_rgb(h, s, v):\n    h = float(h) % 360.0\n    s = float(s)\n    v = float(v)\n    c = v * s\n    x = c * (1 - abs(((h / 60.0) % 2) - 1))\n    m = v - c\n    if h < 60:\n        rp, gp, bp = c, x, 0\n    elif h < 120:\n        rp, gp, bp = x, c, 0\n    elif h < 180:\n        rp, gp, bp = 0, c, x\n    elif h < 240:\n        rp, gp, bp = 0, x, c\n    elif h < 300:\n        rp, gp, bp = x, 0, c\n    else:\n        rp, gp, bp = c, 0, x\n    return int((rp + m) * 255), int((gp + m) * 255), int((bp + m) * 255)\n\n\ndef _clamp255(value):\n    return max(0, min(255, int(value)))\n\n\n# Track effect colors use a smooth rainbow by track number:\n# lowest instrument row = red, highest = violet, evenly spaced in between.\n\ndef track_color_for_index(track_index, brightness=1.0, track_count=None):\n    try:\n        idx = int(track_index)\n    except Exception:\n        idx = 0\n    try:\n        brightness = float(brightness)\n    except Exception:\n        brightness = 1.0\n    brightness = max(0.0, min(1.0, brightness))\n    try:\n        track_count = max(1, int(track_count if track_count is not None else 16))\n    except Exception:\n        track_count = 16\n\n    idx = max(0, min(idx, track_count - 1))\n\n    if track_count == 1:\n        r, g, b = (0, 80, 255)\n    elif track_count == 2:\n        r, g, b = ((0, 80, 255), (255, 0, 0))[idx]\n    elif track_count == 3:\n        r, g, b = ((0, 80, 255), (255, 0, 0), (0, 255, 0))[idx]\n    else:\n        hue = 275.0 * (idx / float(track_count - 1))\n        r, g, b = _hsv_to_rgb(hue, 1.0, brightness)\n        return _clamp255(r), _clamp255(g), _clamp255(b)\n\n    return _clamp255(r * brightness), _clamp255(g * brightness), _clamp255(b * brightness)\n\n\ndef _stable_random_rgb_for_note(midi_note):\n    seed = (int(midi_note) * 1103515245 + 12345) & 0xFFFFFFFF\n    rng = random.Random(seed)\n    return rng.randint(0, 255), rng.randint(0, 255), rng.randint(0, 255)\n\n\ndef _stable_flicker_value(midi_note, t, speed):\n    rate = max(1.0, float(speed))\n    bucket = int(float(t) * rate)\n    seed = (int(midi_note) * 1315423911 + bucket * 2654435761) & 0xFFFFFFFF\n    rng = random.Random(seed)\n    return rng.uniform(0.5, 1.0)\n\n\ndef led_color_for_note(midi_note, t=None, cfg=None, effect=None, track_index=None):\n    if t is None:\n        t = time.time()\n    if cfg is None:\n        cfg = {}\n    if effect is None:\n        effect = cfg.get(\'effect\', \'Solid\')\n\n    bright = max(0, min(100, int(cfg.get(\'brightness\', 100)))) / 100.0\n    speed = cfg.get(\'speed\', 20)\n\n    note = int(midi_note)\n    idx = max(0, min(87, note - 21))\n\n    r = int((int(cfg.get(\'red\', 100)) / 100.0) * 255 * bright)\n    g = int((int(cfg.get(\'green\', 100)) / 100.0) * 255 * bright)\n    b = int((int(cfg.get(\'blue\', 100)) / 100.0) * 255 * bright)\n\n    if effect == \'Track\':\n        r, g, b = track_color_for_index(track_index, bright, cfg.get(\'track_color_count\'))\n\n    elif effect == \'RGB\':\n        sel = idx % 3\n        if sel == 0:\n            r, g, b = int(255 * bright), 0, 0\n        elif sel == 1:\n            r, g, b = 0, int(255 * bright), 0\n        else:\n            r, g, b = 0, 0, int(255 * bright)\n    elif effect == \'Random RGB\':\n        r0, g0, b0 = _stable_random_rgb_for_note(note)\n        r, g, b = int(r0 * bright), int(g0 * bright), int(b0 * bright)\n    elif effect == \'Rainbow Effect\':\n        r, g, b = _hsv_to_rgb((idx / 88.0) * 360.0, 1, 1)\n        r, g, b = int(r * bright), int(g * bright), int(b * bright)\n    elif effect == \'Moving Rainbow\':\n        r, g, b = _hsv_to_rgb((idx * 4 + float(t) * float(speed) * 5) % 360, 1, 1)\n        r, g, b = int(r * bright), int(g * bright), int(b * bright)\n    elif effect == \'Dancing\':\n        phase = (float(t) * (float(speed) / 6.0) + idx * 0.1) % 2.0\n        v = 1.0 - abs(phase - 1.0)\n        r, g, b = _hsv_to_rgb((idx / 88.0) * 360.0, 1, v)\n        r, g, b = int(r * bright), int(g * bright), int(b * bright)\n    elif effect == \'Flicker\':\n        v = _stable_flicker_value(note, float(t), float(speed))\n        r, g, b = _hsv_to_rgb((idx / 88.0) * 360.0, 1, v)\n        r, g, b = int(r * bright), int(g * bright), int(b * bright)\n    elif effect == \'Christmas\':\n        if idx % 2 == 0:\n            r, g, b = int(255 * bright), 0, 0\n        else:\n            r, g, b = 0, int(255 * bright), 0\n\n    return _clamp255(r), _clamp255(g), _clamp255(b)\n\n\ndef idle_led_color_for_index(led_index, t=None, cfg=None, total_leds=218):\n    """Return the idle-strip color for one physical LED index.\n\n    This mirrors the main program\'s idle LED renderer, so the screen keyboard\n    can show the same idle effect/colors as the real light strip while no song\n    is playing.\n    """\n    if t is None:\n        t = time.time()\n    if cfg is None:\n        cfg = {}\n\n    idle_eff = cfg.get(\'idle_effect\', \'Off\')\n    try:\n        speed = float(cfg.get(\'speed\', 20))\n    except Exception:\n        speed = 20.0\n    try:\n        bright = max(0, min(100, int(cfg.get(\'brightness\', 100)))) / 100.0\n    except Exception:\n        bright = 1.0\n\n    i = max(0, min(int(total_leds) - 1, int(led_index)))\n    total_leds = max(1, int(total_leds))\n    mid = total_leds / 2.0\n    phase = (float(t) * speed) % total_leds\n\n    if idle_eff == \'Off\':\n        return None\n    if idle_eff == \'Solid\':\n        r = int((int(cfg.get(\'red\', 100)) / 100.0) * 255 * bright)\n        g = int((int(cfg.get(\'green\', 100)) / 100.0) * 255 * bright)\n        b = int((int(cfg.get(\'blue\', 100)) / 100.0) * 255 * bright)\n        return _clamp255(r), _clamp255(g), _clamp255(b)\n    if idle_eff == \'R->L Rainbow\':\n        hue = ((i + phase) / total_leds) * 360 % 360\n        r, g, b = _hsv_to_rgb(hue, 1, 1)\n        return _clamp255(r * bright), _clamp255(g * bright), _clamp255(b * bright)\n    if idle_eff == \'L->R Rainbow\':\n        hue = ((i - phase) / total_leds) * 360 % 360\n        r, g, b = _hsv_to_rgb(hue, 1, 1)\n        return _clamp255(r * bright), _clamp255(g * bright), _clamp255(b * bright)\n    if idle_eff == \'Rainbow\':\n        dist = abs(i - mid)\n        idx = (dist - (float(t) * speed) % mid) % mid if mid else 0\n        hue = (idx / mid) * 360 if mid else 0\n        r, g, b = _hsv_to_rgb(hue, 1, 1)\n        return _clamp255(r * bright), _clamp255(g * bright), _clamp255(b * bright)\n    if idle_eff == \'RGB Cable\':\n        palette = (\n            (255, 0, 0),\n            (0, 255, 0),\n            (0, 80, 255),\n            (255, 0, 255),\n        )\n        band_count = len(palette)\n        cable_speed = max(1.0, min(100.0, float(speed))) * 0.85\n        p = (((i + float(t) * cable_speed) / max(1.0, float(total_leds))) * band_count) % band_count\n        base = int(p)\n        frac = p - base\n        transition = 0.38\n        if frac < (1.0 - transition):\n            mix = 0.0\n        else:\n            x = (frac - (1.0 - transition)) / transition\n            mix = x * x * (3.0 - 2.0 * x)\n        c0 = palette[base]\n        c1 = palette[(base + 1) % band_count]\n        r = (c0[0] * (1.0 - mix) + c1[0] * mix) * bright\n        g = (c0[1] * (1.0 - mix) + c1[1] * mix) * bright\n        b = (c0[2] * (1.0 - mix) + c1[2] * mix) * bright\n        return _clamp255(r), _clamp255(g), _clamp255(b)\n    if idle_eff == \'RGB Cable Gaps\':\n        palette = (\n            (255, 0, 0),\n            (0, 255, 0),\n            (0, 80, 255),\n            (255, 0, 255),\n        )\n        band_count = len(palette)\n        cable_speed = max(1.0, min(100.0, float(speed))) * 0.85\n        p = (((i - float(t) * cable_speed) / max(1.0, float(total_leds))) * band_count) % band_count\n        base = int(p)\n        frac = p - base\n        color_width = 0.58\n        edge = 0.10\n        if frac >= color_width:\n            return None\n\n        def _smoothstep(x):\n            x = max(0.0, min(1.0, float(x)))\n            return x * x * (3.0 - 2.0 * x)\n\n        intensity = 1.0\n        if frac < edge:\n            intensity = _smoothstep(frac / edge)\n        elif frac > color_width - edge:\n            intensity = _smoothstep((color_width - frac) / edge)\n\n        c = palette[base]\n        return _clamp255(c[0] * bright * intensity), _clamp255(c[1] * bright * intensity), _clamp255(c[2] * bright * intensity)\n    if idle_eff == \'4th of July\':\n        palette = (\n            (255, 0, 0),\n            (255, 255, 255),\n            (0, 80, 255),\n            (255, 255, 255),\n        )\n        band_count = len(palette)\n        patriotic_speed = max(1.0, min(100.0, float(speed))) * 0.75\n        stripe_repeats = 2.5\n        p = (((i - float(t) * patriotic_speed) / max(1.0, float(total_leds))) * band_count * stripe_repeats) % band_count\n        base = int(p)\n        frac = p - base\n        transition = 0.22\n        if frac < (1.0 - transition):\n            mix = 0.0\n        else:\n            x = (frac - (1.0 - transition)) / transition\n            mix = x * x * (3.0 - 2.0 * x)\n        c0 = palette[base]\n        c1 = palette[(base + 1) % band_count]\n        r = (c0[0] * (1.0 - mix) + c1[0] * mix) * bright\n        g = (c0[1] * (1.0 - mix) + c1[1] * mix) * bright\n        b = (c0[2] * (1.0 - mix) + c1[2] * mix) * bright\n        return _clamp255(r), _clamp255(g), _clamp255(b)\n    if idle_eff == \'Flicker\':\n        flicker_rate = 0.5 + (max(1.0, min(100.0, speed)) / 100.0) * 24.5\n        bucket = int(float(t) * flicker_rate)\n        seed = (i * 1103515245 + bucket * 2654435761) & 0xFFFFFFFF\n        rng = random.Random(seed)\n        v = int(255 * rng.uniform(0.35, 1.0) * bright)\n        return _clamp255(v), _clamp255(v), _clamp255(v)\n    if idle_eff == \'Christmas\':\n        dist = abs(i - mid)\n        scroll = (float(t) * speed) % mid if mid else 0\n        idx = (dist - scroll) % mid if mid else 0\n        segment_width = mid / 3.0 if mid else 1.0\n        band = int(idx / segment_width)\n        if band == 1:\n            return 0, _clamp255(255 * bright), 0\n        return _clamp255(255 * bright), 0, 0\n\n    return None\n\n\ndef idle_led_color_for_note(midi_note, t=None, cfg=None, total_leds=218):\n    """Approximate the idle-strip color for one 88-key piano note.\n\n    The physical strip has about 2-3 LEDs per key, so this averages the LEDs\n    assigned to the note. One screen key cannot show multiple LEDs at once,\n    because it is tragically still a rectangle.\n    """\n    note = int(midi_note)\n    if note < VISUALIZER_MIN_NOTE or note > VISUALIZER_MAX_NOTE:\n        return None\n    idx = note - VISUALIZER_MIN_NOTE\n    start = int(idx * int(total_leds) / 88)\n    end = int((idx + 1) * int(total_leds) / 88)\n    if end <= start:\n        end = start + 1\n\n    colors = []\n    for led in range(start, min(end, int(total_leds))):\n        c = idle_led_color_for_index(led, t=t, cfg=cfg, total_leds=total_leds)\n        if c is not None:\n            colors.append(c)\n    if not colors:\n        return None\n    r = sum(c[0] for c in colors) / len(colors)\n    g = sum(c[1] for c in colors) / len(colors)\n    b = sum(c[2] for c in colors) / len(colors)\n    return _clamp255(r), _clamp255(g), _clamp255(b)\n\n\ndef _default_led_cfg():\n    return {\n        \'red\': 100,\n        \'green\': 100,\n        \'blue\': 100,\n        \'brightness\': 100,\n        \'effect\': \'Solid\',\n        \'idle_effect\': \'Off\',\n        \'speed\': 20,\n        \'track_color_count\': 16,\n    }\n\n\ndef read_led_cfg(path):\n    cfg = _default_led_cfg()\n    if path:\n        try:\n            with open(path, \'r\') as f:\n                data = json.load(f)\n            if isinstance(data, dict):\n                cfg.update(data)\n        except Exception:\n            pass\n    return cfg\n\n\ndef parse_midi_notes(midi_path, instrument_indices=None, min_refractory_off=0.075):\n    """Parse visualizer notes at original MIDI timing.\n\n    min_refractory_off is accepted for compatibility but intentionally ignored.\n    The visualizer should match the file/FluidSynth, while the solenoid path\n    handles same-key hardware protection separately.\n    """\n    pm = _safe_pretty_midi(midi_path)\n    selected = set(int(i) for i in instrument_indices) if instrument_indices is not None else None\n    notes = []\n\n    for inst_idx, inst in enumerate(pm.instruments):\n        if selected is not None:\n            if int(inst_idx) not in selected:\n                continue\n        else:\n            if getattr(inst, \'is_drum\', False):\n                continue\n        for n in getattr(inst, \'notes\', []):\n            try:\n                pitch = int(n.pitch)\n                velocity = int(n.velocity)\n                start = float(n.start)\n                end = float(n.end)\n            except Exception:\n                continue\n            if pitch < VISUALIZER_MIN_NOTE or pitch > VISUALIZER_MAX_NOTE:\n                continue\n            if end <= start:\n                end = start + 0.03\n            notes.append({\'start\': float(start), \'end\': float(end), \'note\': int(pitch), \'channel\': int(inst_idx), \'velocity\': int(velocity)})\n\n    try:\n        bpm_guess = float(pm.estimate_tempo())\n        if not bpm_guess or bpm_guess <= 0:\n            bpm_guess = 120.0\n    except Exception:\n        bpm_guess = 120.0\n\n    duration = float(pm.get_end_time())\n    notes.sort(key=lambda n: n[\'start\'])\n    return notes, duration, bpm_guess\n\nclass Backend:\n    def __init__(self, w, h):\n        import pygame\n        self.pygame = pygame\n        self.w = int(w)\n        self.h = int(h)\n        flags = pygame.RESIZABLE | pygame.DOUBLEBUF\n        self.screen = pygame.display.set_mode((self.w, self.h), flags)\n        pygame.display.set_caption(\'MIDI Visualizer\')\n        self.clock = pygame.time.Clock()\n        self.font = pygame.font.SysFont(None, 32)\n\n    def size(self):\n        return self.w, self.h\n\n    def handle_resize(self, ev):\n        if hasattr(ev, \'w\') and hasattr(ev, \'h\'):\n            self.w = int(ev.w)\n            self.h = int(ev.h)\n\n    def clear(self, color):\n        self.screen.fill(color[:3])\n\n    def fill_rect(self, x, y, w, h, color):\n        import pygame\n        rect = pygame.Rect(int(x), int(y), int(w), int(h))\n        if len(color) >= 4 and color[3] < 255:\n            surf = pygame.Surface((max(1, rect.w), max(1, rect.h)), pygame.SRCALPHA)\n            surf.fill(color)\n            self.screen.blit(surf, rect.topleft)\n        else:\n            pygame.draw.rect(self.screen, color[:3], rect)\n\n    def draw_center_text(self, text, y, color=(180, 190, 220)):\n        try:\n            surf = self.font.render(text, True, color)\n            rect = surf.get_rect(center=(self.w // 2, int(y)))\n            self.screen.blit(surf, rect)\n        except Exception:\n            pass\n\n    def present(self):\n        self.pygame.display.flip()\n        self.clock.tick(60)\n\n    def shutdown(self):\n        self.pygame.quit()\n\n\nclass VisualizerState:\n    def __init__(self):\n        self.midi_path = None\n        self.instrument_indices = None\n        self.playback_start_mono = time.monotonic()\n        self.led_config_file = None\n        self.notes = []\n        self.starts = []\n        self.bpm = 120.0\n        self.duration = 0.0\n        self.load_error = None\n        self.signature = None\n        self.start_cursor = 0\n        self.active_notes = []\n        self.live_active_notes = []\n        self.idle_suspended_until = 0.0\n        self.paused = False\n        self.paused_offset = 0.0\n        self.min_refractory_off = 0.075\n        self.track_count = 16\n\n    def now(self):\n        if getattr(self, \'paused\', False):\n            return max(0.0, float(getattr(self, \'paused_offset\', 0.0)))\n        return max(0.0, time.monotonic() - float(self.playback_start_mono or time.monotonic()))\n\n    def reset_cursors(self):\n        now = self.now()\n        self.starts = [n[\'start\'] for n in self.notes]\n        self.start_cursor = bisect_right(self.starts, now)\n        self.active_notes = [n for n in self.notes if n[\'start\'] <= now < n[\'end\']]\n\n    def apply(self, payload):\n        if payload.get(\'quit\'):\n            return \'quit\'\n\n        midi_path = payload.get(\'midi_path\')\n        instr = payload.get(\'instrument_indices\')\n        if instr is not None:\n            instr = [int(x) for x in instr]\n        playback_start = float(payload.get(\'playback_start_mono\') or (time.monotonic()))\n        led_config_file = payload.get(\'led_config_file\')\n        paused = bool(payload.get(\'paused\', False))\n        try:\n            playback_offset = max(0.0, float(payload.get(\'playback_offset\', 0.0)))\n        except Exception:\n            playback_offset = 0.0\n        try:\n            min_refractory_off = max(0.0, float(payload.get(\'min_refractory_off\', 0.075)))\n        except Exception:\n            min_refractory_off = 0.075\n        try:\n            self.track_count = max(1, int(payload.get(\'track_count\', getattr(self, \'track_count\', 16))))\n        except Exception:\n            self.track_count = max(1, int(getattr(self, \'track_count\', 16) or 16))\n\n        # Live keyboard notes are sent while no song is playing. They light the\n        # screen keyboard with the normal Effect and suppress idle colors until\n        # idle_suspended_until has passed.\n        self.live_active_notes = []\n        try:\n            for item in payload.get(\'live_active_notes\') or []:\n                if isinstance(item, dict):\n                    note = int(item.get(\'note\'))\n                    velocity = int(item.get(\'velocity\', 100))\n                else:\n                    note = int(item)\n                    velocity = 100\n                if VISUALIZER_MIN_NOTE <= note <= VISUALIZER_MAX_NOTE:\n                    self.live_active_notes.append({\'note\': note, \'velocity\': velocity})\n        except Exception:\n            self.live_active_notes = []\n        try:\n            self.idle_suspended_until = float(payload.get(\'idle_suspended_until\') or 0.0)\n        except Exception:\n            self.idle_suspended_until = 0.0\n\n        signature = (os.path.abspath(midi_path) if midi_path else None, tuple(instr) if instr is not None else None, round(float(min_refractory_off), 4))\n        same_signature = signature == self.signature\n        same_start = abs(float(self.playback_start_mono or 0.0) - playback_start) < 0.001\n        old_paused = bool(getattr(self, \'paused\', False))\n\n        self.midi_path = midi_path\n        self.instrument_indices = instr\n        self.playback_start_mono = playback_start\n        self.led_config_file = led_config_file\n        self.paused = paused\n        self.paused_offset = playback_offset\n        self.min_refractory_off = min_refractory_off\n\n        if not same_signature:\n            self.signature = signature\n            self.notes = []\n            self.starts = []\n            self.bpm = 120.0\n            self.duration = 0.0\n            self.load_error = None\n            self.start_cursor = 0\n            self.active_notes = []\n\n            if midi_path:\n                try:\n                    self.notes, self.duration, self.bpm = parse_midi_notes(midi_path, instr, min_refractory_off=min_refractory_off)\n                    self.load_error = None\n                except Exception as exc:\n                    self.notes = []\n                    self.starts = []\n                    self.load_error = str(exc)\n\n            self.reset_cursors()\n        elif (not same_start) or (old_paused != paused):\n            self.reset_cursors()\n\n        return \'ok\'\n\n\ndef read_state_shared(shm, last_seq):\n    """Read one JSON state payload from shared memory.\n\n    Header layout, because apparently even two Python processes need a tiny\n    treaty before sharing a dictionary:\n      uint64 sequence, uint64 payload_length, then UTF-8 JSON bytes.\n    Odd sequence values mean the writer is mid-update, so the reader ignores it.\n    """\n    try:\n        buf = shm.buf\n        if len(buf) < 16:\n            return None, last_seq\n        seq1, length1 = struct.unpack_from(\'QQ\', buf, 0)\n        if seq1 == last_seq or (seq1 & 1):\n            return None, last_seq\n        max_len = len(buf) - 16\n        if length1 <= 0 or length1 > max_len:\n            return None, last_seq\n        raw = bytes(buf[16:16 + int(length1)])\n        seq2, length2 = struct.unpack_from(\'QQ\', buf, 0)\n        if seq1 != seq2 or length1 != length2 or (seq2 & 1):\n            return None, last_seq\n        payload = json.loads(raw.decode(\'utf-8\'))\n        return payload, seq2\n    except Exception:\n        return None, last_seq\n\n\ndef is_black_key(midi_note):\n    return int(midi_note) % 12 in (1, 3, 6, 8, 10)\n\n\ndef active_note_numbers(note_items):\n    active = set()\n    for item in note_items or []:\n        try:\n            if isinstance(item, dict):\n                active.add(int(item.get(\'note\')))\n            else:\n                active.add(int(item))\n        except Exception:\n            pass\n    return active\n\n\ndef active_note_track_map(note_items):\n    mapping = {}\n    for item in note_items or []:\n        try:\n            if isinstance(item, dict):\n                mapping[int(item.get(\'note\'))] = int(item.get(\'channel\', 0))\n        except Exception:\n            pass\n    return mapping\n\n\ndef rebuild_x_cache(screen_w, min_note, max_note):\n    white_count = 52\n    white_w = max(1.0, float(screen_w) / white_count)\n    black_w = max(4.0, white_w * 0.62)\n    cache = {}\n\n    white_index = 0\n    for p in range(min_note, max_note + 1):\n        if not is_black_key(p):\n            x = int(white_index * white_w + white_w * 0.12)\n            bar_w = int(max(4, white_w * 0.76))\n            cache[p] = (x, bar_w)\n            white_index += 1\n\n    white_index = 0\n    for p in range(min_note, max_note + 1):\n        if is_black_key(p):\n            x = int(white_index * white_w - black_w * 0.5)\n            bar_w = int(max(4, black_w * 0.82))\n            cache[p] = (x, bar_w)\n        else:\n            white_index += 1\n\n    return cache\n\n\ndef draw_piano_keyboard(backend, screen_w, screen_h, key_top, note_items, cfg, effect, now_wall, min_note, max_note, idle_mode=False):\n    key_top = int(min(max(0, key_top), max(0, screen_h - 8)))\n    key_bottom = int(max(key_top + 8, screen_h - 4))\n    key_h = max(8, key_bottom - key_top)\n    white_count = 52\n    white_w = max(1.0, float(screen_w) / white_count)\n    black_w = max(4.0, white_w * 0.62)\n    black_h = max(8, int(key_h * 0.62))\n    active = active_note_numbers(note_items)\n    active_track_by_note = active_note_track_map(note_items)\n\n    def key_color(p, black=False):\n        if idle_mode:\n            idle_rgb = idle_led_color_for_note(p, t=now_wall, cfg=cfg)\n            if idle_rgb is not None:\n                r, g, b = idle_rgb\n                return (r, g, b, 255)\n            return (8, 8, 12, 255) if black else (232, 232, 224, 255)\n\n        if p in active:\n            r, g, b = led_color_for_note(p, t=now_wall, cfg=cfg, effect=effect, track_index=active_track_by_note.get(p))\n            boost = 25 if black else 45\n            return (min(255, r + boost), min(255, g + boost), min(255, b + boost), 255)\n        return (8, 8, 12, 255) if black else (232, 232, 224, 255)\n\n    white_index = 0\n    for p in range(min_note, max_note + 1):\n        if is_black_key(p):\n            continue\n        x = int(white_index * white_w)\n        w_key = int(max(1, math.ceil((white_index + 1) * white_w) - x))\n        color = key_color(p, black=False)\n        backend.fill_rect(x, key_top, w_key, key_h, color)\n        backend.fill_rect(x, key_top, 1, key_h, (30, 32, 42, 255))\n        white_index += 1\n    backend.fill_rect(0, key_bottom - 2, screen_w, 2, (35, 38, 48, 255))\n\n    white_index = 0\n    for p in range(min_note, max_note + 1):\n        if is_black_key(p):\n            x = int(white_index * white_w - black_w * 0.5)\n            color = key_color(p, black=True)\n            backend.fill_rect(x, key_top, int(black_w), black_h, color)\n            backend.fill_rect(x, key_top, 1, black_h, (0, 0, 0, 255))\n            backend.fill_rect(x + int(black_w) - 1, key_top, 1, black_h, (0, 0, 0, 255))\n        else:\n            white_index += 1\n\n\ndef update_and_draw_particles(backend, particles, dt):\n    write_i = 0\n    for i in range(len(particles)):\n        p = particles[i]\n        p[4] += dt\n        if p[4] >= p[5]:\n            continue\n        p[0] += p[2] * dt\n        p[1] += p[3] * dt\n        p[3] += 900 * dt\n        t = p[4] / p[5]\n        alpha = int(255 * (1.0 - t))\n        backend.fill_rect(p[0], p[1], 3, 3, (p[6], p[7], p[8], alpha))\n        particles[write_i] = p\n        write_i += 1\n    if write_i != len(particles):\n        del particles[write_i:]\n\ndef main():\n    if len(sys.argv) != 3:\n        print(\'Usage: midi_visualizer_helper.py state_shm_name state_shm_size\', file=sys.stderr)\n        sys.exit(2)\n\n    state_shm_name = sys.argv[1]\n    try:\n        state_shm_size = int(sys.argv[2])\n    except Exception:\n        state_shm_size = 262144\n    try:\n        state_shm = shared_memory.SharedMemory(name=state_shm_name)\n    except Exception as exc:\n        print(f\'Could not attach visualizer shared memory: {exc}\', file=sys.stderr)\n        sys.exit(2)\n\n    import pygame\n    pygame.init()\n    try:\n        W = int(os.environ.get(\'MIDI_VISUALIZER_W\', \'960\'))\n        H = int(os.environ.get(\'MIDI_VISUALIZER_H\', \'540\'))\n    except Exception:\n        W, H = 960, 540\n    backend = Backend(W, H)\n\n    state = VisualizerState()\n    last_state_seq = -1\n    last_led_mtime = None\n    led_cfg = _default_led_cfg()\n\n    payload, last_state_seq = read_state_shared(state_shm, last_state_seq)\n    if payload:\n        result = state.apply(payload)\n        if result == \'quit\':\n            try:\n                state_shm.close()\n            except Exception:\n                pass\n            backend.shutdown()\n            return\n\n    base_bg = (8, 8, 14)\n    stars = [{\n        \'x\': random.random(),\n        \'y\': random.random(),\n        \'spd\': 0.12 + random.random() * 0.95,\n        \'sz\': 1 + int(random.random() * 2),\n    } for _ in range(140)]\n    particles = []\n    # Rush/black-MIDI files can throw thousands of notes per second at the screen.\n    # Keep the visualizer real-time instead of letting particles turn into a CPU bonfire.\n    MAX_PARTICLES = 1400\n    MAX_START_PARTICLE_NOTES_PER_FRAME = 28\n    START_PARTICLES_PER_NOTE = 2\n    MAX_ACTIVE_SPARKS_PER_FRAME = 28\n    MAX_FALLING_NOTES_DRAWN = 1800\n    MAX_START_EVENTS_TO_PROCESS_PER_FRAME = 350\n\n    cached_w = None\n    xw_cache = {}\n    min_note = VISUALIZER_MIN_NOTE\n    max_note = VISUALIZER_MAX_NOTE\n    lead = 2.6\n    hit_y_frac = 0.86\n    min_bar_h = 6\n    last_now_wall = time.monotonic()\n    running = True\n\n    while running:\n        payload, last_state_seq = read_state_shared(state_shm, last_state_seq)\n        if payload:\n            old_sig = state.signature\n            result = state.apply(payload)\n            if result == \'quit\':\n                running = False\n                continue\n            if state.signature != old_sig:\n                particles = []\n\n        if state.led_config_file:\n            try:\n                m = os.path.getmtime(state.led_config_file)\n                if m != last_led_mtime:\n                    led_cfg = read_led_cfg(state.led_config_file)\n                    last_led_mtime = m\n            except Exception:\n                pass\n\n        for ev in pygame.event.get():\n            if ev.type == pygame.QUIT:\n                running = False\n            elif ev.type in (pygame.VIDEORESIZE, getattr(pygame, \'WINDOWRESIZED\', pygame.VIDEORESIZE)):\n                backend.handle_resize(ev)\n                cached_w = None\n\n        wall_mono = time.monotonic()\n        dt = max(1e-4, min(0.05, wall_mono - last_now_wall))\n        last_now_wall = wall_mono\n        now = state.now()\n        wall_now = time.time()\n        try:\n            led_cfg[\'track_color_count\'] = int(getattr(state, \'track_count\', 16) or 16)\n        except Exception:\n            led_cfg[\'track_color_count\'] = 16\n\n        w, h = backend.size()\n        hit_y = int(h * hit_y_frac)\n        if cached_w != w:\n            cached_w = w\n            xw_cache = rebuild_x_cache(w, min_note, max_note)\n\n        backend.clear(base_bg)\n\n        for s in stars:\n            s[\'y\'] += s[\'spd\'] * dt * 0.33\n            if s[\'y\'] > 1.0:\n                s[\'y\'] -= 1.0\n                s[\'x\'] = random.random()\n                s[\'spd\'] = 0.12 + random.random() * 0.95\n                s[\'sz\'] = 1 + int(random.random() * 2)\n            backend.fill_rect(int(s[\'x\'] * w), int(s[\'y\'] * h), s[\'sz\'], s[\'sz\'], (55, 65, 92, 255))\n\n        for note in range((min_note // 12) * 12, max_note + 12, 12):\n            if min_note <= note <= max_note:\n                x, _bw = xw_cache.get(note, (0, 10))\n                backend.fill_rect(x, 0, 2, hit_y, (14, 14, 24, 255))\n\n        beat_period = 60.0 / max(1.0, float(state.bpm or 120.0))\n        beat_phase = (now % beat_period) / beat_period if state.midi_path else ((wall_now * 0.25) % 1.0)\n        # Keep the beat grid continuous by wrapping each line instead of letting all six drift off-screen.\n        grid_spacing = max(1.0, hit_y / 6.0)\n        grid_offset = beat_phase * grid_spacing\n        for k in range(7):\n            y = int((grid_offset + k * grid_spacing) % max(1, hit_y))\n            backend.fill_rect(0, y, w, 2, (16, 16, 26, 255))\n\n        pulse = 0.4 + 0.6 * (1.0 - abs(beat_phase - 0.5) * 2.0)\n        glow = int(90 * pulse)\n        backend.fill_rect(0, hit_y - 12, w, 12, (10, 55 + glow // 2, min(255, 150 + glow), 255))\n        backend.fill_rect(0, hit_y, w, 4, (0, 145, 255, 255))\n        idle_keyboard_mode = not bool(state.midi_path)\n        live_notes = state.live_active_notes if idle_keyboard_mode else []\n        idle_suppressed = idle_keyboard_mode and (wall_now < float(getattr(state, \'idle_suspended_until\', 0.0)))\n        if idle_keyboard_mode and live_notes:\n            keyboard_notes = live_notes\n            keyboard_idle_mode = False\n\n            # Live keyboard mode: no falling bar. While a key is held,\n            # continuously emit the same upward particles song playback uses.\n            # Release the key and the particle fountain stops, because somehow\n            # even fireworks need boundaries.\n            for n in live_notes:\n                try:\n                    note = int(n.get(\'note\'))\n                    vel = int(n.get(\'velocity\', 80))\n                except Exception:\n                    continue\n                x, bw = xw_cache.get(note, (0, 10))\n                cx = x + bw * 0.5\n                r, g, b = led_color_for_note(note, t=wall_now, cfg=led_cfg, effect=led_cfg.get(\'effect\', \'Solid\'))\n                emit_count = 2 if vel < 70 else 3\n                for _ in range(emit_count):\n                    particles.append([\n                        cx + (random.random() - 0.5) * bw * 0.7,\n                        hit_y - 2 - random.random() * 5,\n                        (random.random() - 0.5) * (90 + vel * 1.1),\n                        -150 - random.random() * (180 + vel * 2.0),\n                        0.0,\n                        0.16 + random.random() * 0.20,\n                        min(255, r + 70), min(255, g + 70), min(255, b + 70),\n                    ])\n\n        elif idle_keyboard_mode and idle_suppressed:\n            keyboard_notes = []\n            keyboard_idle_mode = False\n        else:\n            keyboard_notes = [] if idle_keyboard_mode else state.active_notes\n            keyboard_idle_mode = idle_keyboard_mode\n\n        draw_piano_keyboard(\n            backend,\n            w,\n            h,\n            hit_y + 6,\n            keyboard_notes,\n            led_cfg,\n            led_cfg.get(\'effect\', \'Solid\'),\n            wall_now,\n            min_note,\n            max_note,\n            idle_mode=keyboard_idle_mode,\n        )\n\n        if not state.midi_path:\n            if len(particles) > MAX_PARTICLES:\n                particles = particles[-MAX_PARTICLES:]\n            update_and_draw_particles(backend, particles, dt)\n            backend.present()\n            continue\n\n        if state.load_error:\n            backend.present()\n            continue\n\n        if not state.notes:\n            backend.present()\n            continue\n\n        if state.duration and now >= float(state.duration) + 0.25:\n            state.active_notes = []\n            state.start_cursor = len(state.notes)\n            update_and_draw_particles(backend, particles, dt)\n            backend.present()\n            continue\n\n        started_particle_notes = 0\n        due_cursor = bisect_right(state.starts, now)\n        due_count = max(0, due_cursor - state.start_cursor)\n        if due_count > MAX_START_EVENTS_TO_PROCESS_PER_FRAME:\n            # We are behind. Fast-forward the cursor to real time instead of\n            # burning seconds spawning particles for notes that should already\n            # have happened. Keep currently-held notes visible, but drop stale\n            # fireworks. Fancy rectangles are not worth desyncing the song.\n            recent_from = max(0, due_cursor - 3000)\n            state.active_notes = [n for n in state.notes[recent_from:due_cursor] if n[\'end\'] > now]\n            state.start_cursor = due_cursor\n        else:\n            while state.start_cursor < len(state.notes) and state.notes[state.start_cursor][\'start\'] <= now:\n                n = state.notes[state.start_cursor]\n                if n[\'end\'] > now:\n                    state.active_notes.append(n)\n                    x, bw = xw_cache.get(n[\'note\'], (0, 10))\n                    cx = x + bw * 0.5\n                    r, g, b = led_color_for_note(n[\'note\'], t=wall_now, cfg=led_cfg, effect=led_cfg.get(\'effect\', \'Solid\'), track_index=n.get(\'channel\'))\n                    if started_particle_notes < MAX_START_PARTICLE_NOTES_PER_FRAME:\n                        started_particle_notes += 1\n                        for _ in range(START_PARTICLES_PER_NOTE):\n                            ang = random.random() * math.tau\n                            spd = 120 + random.random() * 260\n                            particles.append([\n                                cx, hit_y,\n                                math.cos(ang) * spd,\n                                -abs(math.sin(ang) * spd) * (0.7 + random.random() * 0.6),\n                                0.0,\n                                0.18 + random.random() * 0.18,\n                                r, g, b,\n                            ])\n                state.start_cursor += 1\n\n        if state.active_notes:\n            state.active_notes = [n for n in state.active_notes if n[\'end\'] > now]\n\n        i0 = bisect_right(state.starts, now)\n        i1 = bisect_right(state.starts, now + lead)\n\n        visible_notes = state.notes[i0:i1]\n        if len(visible_notes) > MAX_FALLING_NOTES_DRAWN:\n            step = max(1, int(math.ceil(len(visible_notes) / float(MAX_FALLING_NOTES_DRAWN))))\n            visible_notes = visible_notes[::step]\n\n        for n in visible_notes:\n            start = n[\'start\']\n            end = n[\'end\']\n            dur = max(0.02, end - start)\n            head_y = hit_y - ((start - now) / lead) * hit_y\n            bar_h = max(min_bar_h, int((dur / lead) * hit_y))\n            top_y = int(head_y - bar_h)\n            bottom_y = int(head_y)\n            if bottom_y < 0 or top_y > hit_y + 40:\n                continue\n            x, bw = xw_cache.get(n[\'note\'], (0, 10))\n            r, g, b = led_color_for_note(n[\'note\'], t=wall_now, cfg=led_cfg, effect=led_cfg.get(\'effect\', \'Solid\'), track_index=n.get(\'channel\'))\n            near = max(0.0, 1.0 - abs(head_y - hit_y) / 180.0)\n            rr = min(255, int(r + near * 55))\n            gg = min(255, int(g + near * 55))\n            bb = min(255, int(b + near * 55))\n            backend.fill_rect(x, top_y, bw, max(2, bottom_y - top_y), (rr, gg, bb, 255))\n\n        active_spark_budget = MAX_ACTIVE_SPARKS_PER_FRAME\n        for n in state.active_notes:\n            remaining = max(0.0, n[\'end\'] - now)\n            if remaining <= 0:\n                continue\n            bar_h = max(min_bar_h, int((remaining / lead) * hit_y))\n            top_y = int(hit_y - bar_h)\n            x, bw = xw_cache.get(n[\'note\'], (0, 10))\n            r, g, b = led_color_for_note(n[\'note\'], t=wall_now, cfg=led_cfg, effect=led_cfg.get(\'effect\', \'Solid\'), track_index=n.get(\'channel\'))\n            backend.fill_rect(x, top_y, bw, max(2, hit_y - top_y),\n                              (min(255, r + 45), min(255, g + 45), min(255, b + 45), 255))\n            vel = int(n.get(\'velocity\', 80))\n            sparks = 1 if vel < 50 else 2\n            if active_spark_budget > 0 and random.random() < 0.25:\n                active_spark_budget -= 1\n                for _ in range(min(sparks, 1)):\n                    particles.append([\n                        x + bw * (0.2 + random.random() * 0.6),\n                        hit_y - random.random() * 6,\n                        (random.random() - 0.5) * 120,\n                        -120 - random.random() * 200,\n                        0.0,\n                        0.12 + random.random() * 0.18,\n                        min(255, r + 70), min(255, g + 70), min(255, b + 70),\n                    ])\n\n        draw_piano_keyboard(\n            backend,\n            w,\n            h,\n            hit_y + 6,\n            state.active_notes,\n            led_cfg,\n            led_cfg.get(\'effect\', \'Solid\'),\n            wall_now,\n            min_note,\n            max_note,\n        )\n\n        if len(particles) > MAX_PARTICLES:\n            particles = particles[-MAX_PARTICLES:]\n\n        update_and_draw_particles(backend, particles, dt)\n\n        backend.present()\n\n    try:\n        state_shm.close()\n    except Exception:\n        pass\n    backend.shutdown()\n\n\nif __name__ == \'__main__\':\n    main()\n'

def _ensure_visualizer_helper() -> str:
    """Write the standalone visualizer helper next to midi_gui.py and return its path."""
    helper_path = os.path.join(os.path.dirname(__file__), "midi_visualizer_helper.py")
    try:
        old = None
        if os.path.exists(helper_path):
            with open(helper_path, "r") as f:
                old = f.read()
        if old != _VISUALIZER_HELPER_CODE:
            with open(helper_path, "w") as f:
                f.write(_VISUALIZER_HELPER_CODE)
            try:
                os.chmod(helper_path, 0o755)
            except Exception:
                pass
    except Exception as e:
        print(f"[Visualizer] Could not write helper script: {e}")
    return helper_path


class _VisualizerTopProxy:
    """Compatibility shim so existing toggle/on_close code can ask winfo_exists()."""
    def __init__(self, owner):
        self.owner = owner

    def winfo_exists(self):
        return self.owner.is_alive()


class VisualizerWindow:
    """
    Persistent pygame visualizer helper.

    The helper process stays alive. The main GUI writes a tiny state payload
    into shared memory whenever the song, seek position, or instrument selection
    changes, and the visualizer reloads inside the same window instead of
    closing/reopening. No more state JSON file flapping around like confetti.
    """
    def __init__(self, gui):
        self.gui = gui
        self.process = None
        self.top = _VisualizerTopProxy(self)
        self.midi_path = None
        self.state_shm_size = 262144
        self._state_lock = threading.Lock()
        self._state_seq = 0
        self.state_shm = shared_memory.SharedMemory(create=True, size=self.state_shm_size)
        try:
            struct.pack_into("QQ", self.state_shm.buf, 0, 0, 0)
        except Exception:
            pass

        # Full-width visualizer in the computed bottom band.
        # It shares one layout calculation with the Tk player and Instrument Mixer
        # so the three windows tile the screen instead of playing bumper cars.
        layout = _compute_app_window_layout(gui)
        self.viz_w = layout["viz_w"]
        self.viz_h = layout["viz_h"]
        self.viz_x = layout["viz_x"]
        self.viz_y = layout["viz_y"]

        # Use the actual mapped Tk player window bottom, then add clearance
        # for the visualizer title bar. SDL positions the client/drawing area,
        # so the title bar appears above the requested y position. Window
        # managers: the gift that keeps taking.
        try:
            gui.update_idletasks()
            measured_bottom = int(gui.winfo_rooty() + gui.winfo_height())
            screen_h = int(gui.winfo_screenheight())
            visualizer_titlebar_clearance = 24
            if 100 <= measured_bottom <= screen_h - 120:
                self.viz_y = measured_bottom + visualizer_titlebar_clearance
                self.viz_h = max(120, screen_h - self.viz_y)
        except Exception as exc:
            print(f"[WARN] Could not measure player bottom for visualizer placement: {exc}")

        self._start_process()
        self.update_from_gui()

    def _start_process(self):
        helper_path = _ensure_visualizer_helper()
        env = os.environ.copy()
        env["SDL_VIDEO_WINDOW_POS"] = f"{self.viz_x},{self.viz_y}"
        env["MIDI_VISUALIZER_W"] = str(getattr(self, "viz_w", 960))
        env["MIDI_VISUALIZER_H"] = str(getattr(self, "viz_h", 540))
        if getattr(self, "state_shm", None) is None:
            self.state_shm = shared_memory.SharedMemory(create=True, size=self.state_shm_size)
            self._state_seq = 0
            try:
                struct.pack_into("QQ", self.state_shm.buf, 0, 0, 0)
            except Exception:
                pass
        self.process = subprocess.Popen(
            [sys.executable, helper_path, self.state_shm.name, str(self.state_shm_size)],
            env=env,
            stdout=None,
            stderr=None,
        )

    def _write_state(self, payload: dict):
        payload["version"] = time.time()
        try:
            data = json.dumps(payload, separators=(",", ":")).encode("utf-8")
        except Exception as e:
            print(f"[Visualizer] Could not serialize state payload: {e}")
            return

        try:
            with self._state_lock:
                shm = getattr(self, "state_shm", None)
                if shm is None:
                    return
                max_len = int(self.state_shm_size) - 16
                if len(data) > max_len:
                    print(f"[Visualizer] State payload too large for shared memory ({len(data)} > {max_len}); skipping update")
                    return
                # Odd sequence = writer active. Even sequence = stable payload.
                odd_seq = int(getattr(self, "_state_seq", 0)) + 1
                if not (odd_seq & 1):
                    odd_seq += 1
                struct.pack_into("QQ", shm.buf, 0, odd_seq, 0)
                shm.buf[16:16 + len(data)] = data
                even_seq = odd_seq + 1
                struct.pack_into("QQ", shm.buf, 0, even_seq, len(data))
                self._state_seq = even_seq
        except Exception as e:
            print(f"[Visualizer] Could not write shared-memory state: {e}")

    def _payload_from_gui(self):
        current_song = getattr(self.gui, "currently_playing", None)
        midi_path = str(current_song) if current_song else None
        self.midi_path = midi_path

        try:
            if midi_path and hasattr(self.gui, "_current_playback_offset"):
                current_offset = float(self.gui._current_playback_offset())
            else:
                current_offset = float(self.gui.scrub_slider.get()) if midi_path else 0.0
        except Exception:
            current_offset = 0.0

        try:
            paused = bool(midi_path and self.gui.playback_thread.is_paused())
        except Exception:
            paused = False

        playback_start_mono = getattr(self.gui, "_visualizer_playback_start_mono", None)
        waiting_for_physical_start = bool(midi_path and getattr(self.gui, "_visualizer_waiting_for_physical_start", False))
        if playback_start_mono is None:
            playback_start_mono = time.monotonic() - current_offset
        if waiting_for_physical_start:
            paused = True
        instrument_indices = get_instrument_settings_for_song(midi_path).get("enabled_indices", []) if midi_path else []

        live_active = []
        try:
            if not midi_path:
                for note, velocity in getattr(self.gui, "live_keyboard_active_notes", {}).items():
                    live_active.append({"note": int(note), "velocity": int(velocity)})
        except Exception:
            live_active = []

        try:
            idle_suspended_until = float(getattr(self.gui, "idle_effect_pause_until", 0.0))
        except Exception:
            idle_suspended_until = 0.0

        try:
            track_count = self.gui._track_count_for_song(midi_path) if midi_path else int(_led_cfg.get("track_color_count", current_track_color_count))
            _set_current_track_color_count(track_count)
        except Exception:
            track_count = int(_led_cfg.get("track_color_count", current_track_color_count))

        return {
            "midi_path": midi_path,
            "playback_start_mono": playback_start_mono,
            "playback_offset": current_offset,
            "paused": paused,
            "instrument_indices": instrument_indices,
            "led_config_file": LED_CONFIG_FILE,
            "live_active_notes": live_active,
            "idle_suspended_until": idle_suspended_until,
            "min_refractory_off": float(MIN_REFRACTORY_OFF),
            "track_count": int(track_count),
            "waiting_for_physical_start": waiting_for_physical_start,
            "pos": [self.viz_x, self.viz_y],
            "size": [getattr(self, "viz_w", 960), getattr(self, "viz_h", 540)],
        }

    def update_from_gui(self):
        if not self.is_alive():
            self._start_process()
        self._write_state(self._payload_from_gui())

    def is_alive(self):
        return bool(self.process is not None and self.process.poll() is None)

    def remember_geometry(self):
        pass

    def close(self):
        try:
            self._write_state({"quit": True})
        except Exception:
            pass
        try:
            if self.process is not None and self.process.poll() is None:
                self.process.terminate()
                try:
                    self.process.wait(timeout=1.5)
                except subprocess.TimeoutExpired:
                    self.process.kill()
                    self.process.wait(timeout=1.0)
        except Exception:
            pass
        try:
            if getattr(self, "state_shm", None) is not None:
                self.state_shm.close()
                self.state_shm.unlink()
                self.state_shm = None
        except FileNotFoundError:
            self.state_shm = None
        except Exception as e:
            print(f"[Visualizer] Could not clean up shared memory: {e}")


# --------------------------------------------------------------------
class TouchListboxScrollbar(tk.Canvas):
    """Wide touch-friendly scrollbar with arrows and a large draggable thumb.

    This is a custom canvas scrollbar so we can make the touch target much
    larger than Tk's native scrollbar thumb. It includes top/bottom arrows
    because touch screens deserve buttons bigger than decorative dust.
    """
    def __init__(self, parent, listbox, width=72, min_thumb=150,
                 trough="#151515", thumb="#6f6f6f", active_thumb="#9a9a9a",
                 arrow_bg="#202020", arrow_active="#2d2d2d", arrow_fg="#d0d0d0", **kwargs):
        super().__init__(
            parent,
            width=int(width),
            bg=trough,
            highlightthickness=0,
            bd=0,
            relief="flat",
            **kwargs,
        )
        self.listbox = listbox
        self.min_thumb = int(min_thumb)
        self.trough = trough
        self.thumb = thumb
        self.active_thumb = active_thumb
        self.arrow_bg = arrow_bg
        self.arrow_active = arrow_active
        self.arrow_fg = arrow_fg
        self.first = 0.0
        self.last = 1.0
        self._drag_offset = 0
        self._dragging = False
        self._pressed_arrow = None
        self._repeat_after = None

        self.bind("<Configure>", lambda _e: self._redraw())
        self.bind("<Button-1>", self._on_press)
        self.bind("<B1-Motion>", self._on_drag)
        self.bind("<ButtonRelease-1>", self._on_release)

    def set(self, first, last):
        try:
            self.first = max(0.0, min(1.0, float(first)))
            self.last = max(0.0, min(1.0, float(last)))
        except Exception:
            self.first, self.last = 0.0, 1.0
        if self.last < self.first:
            self.first, self.last = self.last, self.first
        self._redraw()

    def _arrow_height(self):
        w = max(1, int(self.winfo_width()))
        h = max(1, int(self.winfo_height()))
        # Big enough for fingers, but never allowed to eat the whole scrollbar.
        return max(42, min(70, w, max(20, h // 5)))

    def _track_geometry(self):
        h = max(1, int(self.winfo_height()))
        arrow_h = self._arrow_height()
        track_top = arrow_h
        track_bottom = max(track_top + 1, h - arrow_h)
        track_h = max(1, track_bottom - track_top)
        return arrow_h, track_top, track_bottom, track_h

    def _thumb_geometry(self):
        arrow_h, track_top, _track_bottom, track_h = self._track_geometry()
        visible = max(0.001, min(1.0, self.last - self.first))

        # Touchscreen mode: keep the draggable thumb square-ish instead of
        # stretching it into a long proportional rectangle.
        w = max(1, int(self.winfo_width()))
        thumb_h = track_h if visible >= 0.999 else min(track_h, max(48, min(96, w)))

        movable = max(1, track_h - thumb_h)
        if visible >= 0.999:
            y = track_top
        else:
            y = track_top + int(round((self.first / max(0.001, 1.0 - visible)) * movable))
        y = max(track_top, min(track_top + movable, y))
        return y, thumb_h, visible, movable, track_top

    def _draw_arrow(self, top=True):
        w = max(1, int(self.winfo_width()))
        h = max(1, int(self.winfo_height()))
        arrow_h = self._arrow_height()
        y0 = 0 if top else h - arrow_h
        y1 = arrow_h if top else h
        which = "up" if top else "down"
        bg = self.arrow_active if self._pressed_arrow == which else self.arrow_bg
        self.create_rectangle(0, y0, w, y1, fill=bg, outline="#303030")

        cx = w / 2.0
        cy = (y0 + y1) / 2.0
        tri_w = max(12, min(28, int(w * 0.38)))
        tri_h = max(8, min(18, int(arrow_h * 0.28)))
        if top:
            pts = (cx, cy - tri_h / 2, cx - tri_w / 2, cy + tri_h / 2, cx + tri_w / 2, cy + tri_h / 2)
        else:
            pts = (cx, cy + tri_h / 2, cx - tri_w / 2, cy - tri_h / 2, cx + tri_w / 2, cy - tri_h / 2)
        self.create_polygon(*pts, fill=self.arrow_fg, outline=self.arrow_fg)

    def _redraw(self):
        self.delete("all")
        w = max(1, int(self.winfo_width()))
        h = max(1, int(self.winfo_height()))
        self.create_rectangle(0, 0, w, h, fill=self.trough, outline=self.trough)
        self._draw_arrow(top=True)
        self._draw_arrow(top=False)

        y, thumb_h, _visible, _movable, _track_top = self._thumb_geometry()
        fill = self.active_thumb if self._dragging else self.thumb
        pad = 7
        self.create_rectangle(
            pad, y + 5,
            max(pad + 1, w - pad), max(y + 12, y + thumb_h - 5),
            fill=fill,
            outline="#3a3a3a",
            width=1,
        )
        # Large grab grooves so the thumb reads as draggable on a touch display.
        cy = y + thumb_h // 2
        for off in (-16, -8, 0, 8, 16):
            self.create_line(pad + 12, cy + off, w - pad - 12, cy + off, fill="#3f3f3f", width=2)

    def _move_to_y(self, y):
        thumb_y, thumb_h, visible, movable, track_top = self._thumb_geometry()
        if visible >= 0.999:
            self.listbox.yview_moveto(0.0)
            return
        pos = max(track_top, min(track_top + movable, int(y)))
        first = ((pos - track_top) / float(movable)) * max(0.0, 1.0 - visible)
        self.listbox.yview_moveto(first)

    def _scroll_arrow_once(self, direction):
        try:
            self.listbox.yview_scroll(int(direction) * 3, "units")
        except Exception:
            pass

    def _repeat_arrow_scroll(self):
        if self._pressed_arrow == "up":
            self._scroll_arrow_once(-1)
            self._repeat_after = self.after(110, self._repeat_arrow_scroll)
        elif self._pressed_arrow == "down":
            self._scroll_arrow_once(1)
            self._repeat_after = self.after(110, self._repeat_arrow_scroll)

    def _cancel_repeat(self):
        if self._repeat_after is not None:
            try:
                self.after_cancel(self._repeat_after)
            except Exception:
                pass
            self._repeat_after = None

    def _on_press(self, event):
        arrow_h, _track_top, track_bottom, _track_h = self._track_geometry()
        if event.y < arrow_h:
            self._pressed_arrow = "up"
            self._scroll_arrow_once(-1)
            self._cancel_repeat()
            self._repeat_after = self.after(350, self._repeat_arrow_scroll)
            self._redraw()
            return "break"
        if event.y >= track_bottom:
            self._pressed_arrow = "down"
            self._scroll_arrow_once(1)
            self._cancel_repeat()
            self._repeat_after = self.after(350, self._repeat_arrow_scroll)
            self._redraw()
            return "break"

        thumb_y, thumb_h, _visible, _movable, _track_top = self._thumb_geometry()
        self._dragging = True
        if thumb_y <= event.y <= thumb_y + thumb_h:
            self._drag_offset = event.y - thumb_y
        else:
            self._drag_offset = thumb_h // 2
            self._move_to_y(event.y - self._drag_offset)
        self._redraw()
        return "break"

    def _on_drag(self, event):
        if self._pressed_arrow:
            return "break"
        self._move_to_y(event.y - self._drag_offset)
        return "break"

    def _on_release(self, _event):
        self._cancel_repeat()
        self._pressed_arrow = None
        self._dragging = False
        self._redraw()
        return "break"

class MidiGUI(tk.Tk):
    def __init__(self, playback_thread: PlaybackThread):
        super().__init__()

        # Compute a tiled screen layout: player and mixer on top, visualizer below.
        # The layout accounts for title bars so the windows do not overlap.
        self._app_layout = _compute_app_window_layout(self)
        self.geometry(
            f"{self._app_layout['player_w']}x{self._app_layout['top_h']}"
            f"+{self._app_layout['player_x']}+{self._app_layout['top_y']}"
        )
        self.resizable(False, False)
        self.pack_propagate(False)
        self.title("MIDI Solenoid Player")

        # Visualizer / instrument mixer window tracking
        self._viz_geometry = None
        self._instrument_mixer_win = None
        self._instrument_mixer_song_path = None
        self._auto_open_windows = True

        # Dark theme
        BG = "#1e1e1e"
        PANEL = "#232323"
        ACCENT = "#333333"
        FG = "#e6e6e6"
        SEL_BG = "#3f3f3f"

        self.configure(bg=BG)
        style = ttk.Style(self)
        style.theme_use("clam")
        style.configure(".", background=BG, foreground=FG)
        style.configure("TFrame", background=BG)
        style.configure("TLabel", background=BG, foreground=FG)
        style.configure("TButton", background=ACCENT, foreground=FG, borderwidth=0, padding=6)
        style.configure("Compact.TButton", background=ACCENT, foreground=FG, borderwidth=0, padding=(4, 10), font=("TkDefaultFont", 9))
        style.configure("RecordActive.TButton", background="#8a2020", foreground="#ffffff", borderwidth=0, padding=(4, 10), font=("TkDefaultFont", 9, "bold"))
        style.configure("Search.TEntry", foreground="#000000", fieldbackground="#ffffff")
        style.map("TButton", background=[("active", SEL_BG)])
        style.map("Compact.TButton", background=[("active", SEL_BG)])
        style.map("RecordActive.TButton", background=[("active", "#b62b2b"), ("disabled", "#8a2020")], foreground=[("disabled", "#ffffff")])

        # Make LED Effect combobox black text on white (like the Search field)
        style.configure("LED.TCombobox",
                        foreground="#000000",
                        fieldbackground="#ffffff",
                        background="#ffffff")
        style.map("LED.TCombobox",
                foreground=[("readonly", "#000000")],
                fieldbackground=[("readonly", "#ffffff")],
                background=[("readonly", "#ffffff")])

        # Also style the drop-down list colors for readability
        self.option_add("*TCombobox*Listbox.background", "#ffffff")
        self.option_add("*TCombobox*Listbox.foreground", "#000000")
        self.option_add("*TCombobox*Listbox.selectBackground", SEL_BG)
        self.option_add("*TCombobox*Listbox.selectForeground", FG)

        self.playback_thread = playback_thread
        self.queue_files = []
        self.currently_playing = None
        self.favorite_song_path = str(_cfg.get("favorite_song", "") or "")
        self._favorite_press_time = None
        self._favorite_hold_after = None
        self._favorite_hold_fired = False
        self.audio_process = None
        self.temp_audio_file = None  # for trimmed files on seeks
        self._current_audio_filter_audio = None
        self._deferred_audio_start = None
        self._instrument_change_job_id = 0
        self._pending_instrument_change_after = None
        self._pending_paused_instrument_restart = False
        self._pending_paused_instrument_song = None
        self.led_worker = LEDWorker(self)
        self.play_history_logger = BackgroundSongPlayLogger(PLAY_HISTORY_CSV_FILE)
        self.play_history_logger.start()

        # Keyboard recording state. Visible only when REAL_PIANO == 0.
        self.recordings_folder = KEYBOARD_RECORDINGS_DIR
        self.recording_midi_in_port = None
        self.recording = False
        self.recording_start = None
        self.recording_events = []
        self.recording_active_notes = {}
        self.recording_input_name = ""
        self.current_recording_path = None
        self.recording_program = DEFAULT_RECORDING_PROGRAM
        self._last_recording_input_open_attempt = 0.0

        # Live keyboard display/LED state used when REAL_PIANO == 0.
        # These notes do not get forwarded to MIDI output or FluidSynth. They only
        # light the screen/strip and, when recording, get saved into the MIDI file.
        self.live_keyboard_active_notes = {}  # note -> velocity
        self.live_keyboard_held_notes = set()
        self.live_keyboard_note_expiry = {}
        self.idle_effect_pause_until = 0.0
        self._idle_resume_after = None
        self._live_visual_update_after = None

        # Song display name -> actual path. Needed now that keyboard recordings live in a subfolder.
        self._song_path_by_display = {}

        # Slider / timekeeping
        self.current_duration = 0.0
        self.playback_start_time = None
        # Stable monotonic clock used by the external visualizer. Recomputing
        # this from wall time on every state write made pause/resume drift like
        # a shopping cart with one cursed wheel.
        self._visualizer_playback_start_mono = None
        self._visualizer_waiting_for_physical_start = False
        self._playback_generation = 0
        self.scrub_dragging = False
        self._pause_wallclock = None
        self._loading_song_playback_settings = False

        root = ttk.Frame(self, padding=10)
        root.pack(fill=tk.BOTH, expand=True)

        # Left: Songs header + Search + List + Bottom buttons (grid so buttons never get cut off)
        left = ttk.Frame(root, width=min(420, max(380, int(self._app_layout.get("player_w", 960) * 0.43))))
        left.pack(side=tk.LEFT, fill=tk.BOTH, expand=False)
        left.pack_propagate(False)
        left.grid_propagate(False)

        # The list row expands, buttons stay fixed at the bottom
        left.grid_columnconfigure(0, weight=1)
        left.grid_rowconfigure(2, weight=1)   # row 2 (list) grows/shrinks

        # Header
        ttk.Label(left, text="Songs").grid(row=0, column=0, pady=(0, 4), sticky="n")

        # Search row
        search_row = ttk.Frame(left)
        search_row.grid(row=1, column=0, sticky="ew", pady=(0, 4))
        ttk.Label(search_row, text="Search:").pack(side=tk.LEFT)
        self.search_entry = ttk.Entry(search_row, style="Search.TEntry")
        self.search_entry.pack(side=tk.LEFT, padx=(6, 0), fill="x", expand=True)
        self.search_entry.bind("<KeyRelease>", self.search_songs)

        # Touchscreen on-screen keyboard behavior.
        self.search_entry.bind("<FocusIn>", lambda _e: _set_touchscreen_keyboard_visible(True), add="+")
        self.search_entry.bind("<FocusOut>", lambda _e: _set_touchscreen_keyboard_visible(False), add="+")
        self.search_entry.bind("<Return>", lambda _e: (_set_touchscreen_keyboard_visible(False), self.focus_set()), add="+")
        self.search_entry.bind("<Escape>", lambda _e: (_set_touchscreen_keyboard_visible(False), self.focus_set()), add="+")

        # If the touchscreen user taps anywhere outside Search, remove the text
        # cursor from Search and hide the on-screen keyboard. Tkinter does not
        # do this automatically for clicks on plain frames/labels, because why
        # would clicking away mean clicking away. Absurd little widget kingdom.
        def _hide_osk_if_click_outside_search(event):
            try:
                if event.widget is self.search_entry:
                    return

                def _hide_after_click():
                    try:
                        _set_touchscreen_keyboard_visible(False)
                        if self.focus_get() is self.search_entry:
                            self.focus_set()
                    except Exception:
                        pass

                self.after_idle(_hide_after_click)
            except Exception:
                pass

        self.bind_all("<Button-1>", _hide_osk_if_click_outside_search, add="+")

        # List + scrollbar (this is the only thing that expands vertically)
        left_list_frame = ttk.Frame(left)
        left_list_frame.grid(row=2, column=0, sticky="nsew")

        self.file_listbox = tk.Listbox(
            left_list_frame,
            bg=PANEL, fg=FG,
            selectbackground=SEL_BG, selectforeground=FG,
            highlightthickness=0, bd=0, relief="flat",
            activestyle="none",
            font=("TkDefaultFont", 15)
        )
        self.file_listbox.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        self.file_listbox.bind("<Double-1>", lambda e: self.add_selected())

        # Wide touch scrollbar with a minimum thumb size.
        # Native Tk scrollbars can be made wider, but their thumb still gets tiny
        # with a long song list, which is rude to touch screens and human fingers.
        left_scrollbar = TouchListboxScrollbar(
            left_list_frame,
            self.file_listbox,
            width=72,
            min_thumb=150,
        )
        left_scrollbar.pack(side=tk.RIGHT, fill=tk.Y)
        self.file_listbox.config(yscrollcommand=left_scrollbar.set)

        # --- Buttons at bottom ---
        btns_row = ttk.Frame(left)
        btns_row.grid(row=3, column=0, sticky="ew", pady=(4,0))   # put under list row
        for col in range(4):
            btns_row.grid_columnconfigure(col, weight=1, uniform="song_buttons")

        add_all_btn = ttk.Button(btns_row, text="Add All", command=self.add_all_random)
        add_btn = ttk.Button(btns_row, text="Add Queue", command=self.add_selected)
        rename_btn = ttk.Button(btns_row, text="Rename", command=self.rename_selected_song)
        delete_btn = ttk.Button(btns_row, text="Delete", command=self.delete_selected_song)

        for col, btn in enumerate((add_all_btn, add_btn, rename_btn, delete_btn)):
            btn.grid(row=0, column=col, sticky="ew", padx=2)

        # Right: status + controls + sliders + queue
        right = ttk.Frame(root)
        right.pack(side=tk.LEFT, fill=tk.BOTH, expand=True, padx=(12,0))

        # Currently Playing (top, centered)
        self.status = ttk.Label(right, text="Currently Playing: (none)")
        self.status.pack(anchor="center", pady=(0,6))

        # Controls area (centered). In keyboard-test mode keep everything on one
        # compact row so the LED controls below do not get shoved off-screen. UI
        # layout: always one button away from becoming furniture Tetris.
        controls = ttk.Frame(right)
        controls.pack(fill="x", pady=(0,6))

        transport_row = ttk.Frame(controls)
        transport_row.pack(fill="x", anchor="center")

        compact_controls = not REAL_PIANO
        top_button_style = "Compact.TButton" if compact_controls else "TButton"
        stop_text = "Stop" if compact_controls else "Stop Current"
        inst_text = "Inst" if compact_controls else "Instruments"
        viz_text = "Viz" if compact_controls else "Visualizer"

        # Keyboard mode has more controls, so use a true equal-width grid instead
        # of pack. pack asks every button how wide it wants to be, then lets the
        # row overflow like a shopping cart with a bad wheel. The grid below forces
        # all controls to share the available width.
        self.pause_btn = ttk.Button(transport_row, text="Pause", command=self.toggle_pause, style=top_button_style, width=5)
        self.stop_btn = ttk.Button(transport_row, text=stop_text, command=self.stop_current, style=top_button_style, width=5)
        self.instrument_btn = ttk.Button(transport_row, text=inst_text, command=self.open_instrument_mixer, style=top_button_style, width=5)
        self.viz_btn = ttk.Button(transport_row, text=viz_text, command=self.toggle_visualizer, style=top_button_style, width=5)
        self.exit_btn = ttk.Button(transport_row, text="Exit", command=self.on_close, style=top_button_style, width=5)

        self.record_btn = None
        self.stop_record_btn = None  # old name kept so older helper code does not trip over itself
        self.save_recording_btn = None

        if not REAL_PIANO:
            self.record_btn = ttk.Button(transport_row, text="Rec", command=self.toggle_keyboard_recording, style="Compact.TButton", width=5)
            self.save_recording_btn = ttk.Button(transport_row, text="Save", command=self.save_keyboard_recording, state=tk.DISABLED, style="Compact.TButton", width=5)
            transport_buttons = [
                self.pause_btn,
                self.stop_btn,
                self.instrument_btn,
                self.viz_btn,
                self.record_btn,
                self.save_recording_btn,
                self.exit_btn,
            ]
        else:
            transport_buttons = [
                self.pause_btn,
                self.stop_btn,
                self.instrument_btn,
                self.viz_btn,
                self.exit_btn,
            ]

        for col, btn in enumerate(transport_buttons):
            transport_row.grid_columnconfigure(col, weight=1, uniform="transport")
            btn.grid(row=0, column=col, sticky="ew", padx=2, pady=(0, 0))


        # --- Position + Volume sliders (perfectly aligned & centered) ---
        SLIDER_LENGTH = 260
        PAD = 4
        LEFT_W  = 12  # align slider labels
        RIGHT_W = 6   # wide enough for "100%" and "m:ss"

        sliders = ttk.Frame(right)
        sliders.pack(anchor="center", pady=(0, 4))

        # shared 3 columns
        sliders.grid_columnconfigure(0, weight=0)
        sliders.grid_columnconfigure(1, weight=0)
        sliders.grid_columnconfigure(2, weight=0)

        # ---- Position row
        self.current_time_label = ttk.Label(sliders, text="0:00", anchor="e", width=LEFT_W)
        self.current_time_label.grid(row=0, column=0, padx=(0, PAD), sticky="e")

        self.scrub_slider = tk.Scale(
            sliders, from_=0, to=100, orient=tk.HORIZONTAL, length=SLIDER_LENGTH,
            resolution=0.1, bg=BG, fg=FG, troughcolor=ACCENT,
            highlightthickness=0, showvalue=0
        )
        self.scrub_slider.grid(row=0, column=1, sticky="w")
        self.scrub_slider.bind("<ButtonPress-1>", self.on_slider_press)
        self.scrub_slider.bind("<ButtonRelease-1>", self.on_slider_release)
        self.scrub_slider.bind("<B1-Motion>", lambda e: setattr(self, "scrub_dragging", True))

        self.total_time_label = ttk.Label(sliders, text="0:00", anchor="w", width=RIGHT_W)
        self.total_time_label.grid(row=0, column=2, padx=(PAD, 0), sticky="w")

        # ---- Volume row
        self.vol_label_left = ttk.Label(sliders, text="Volume", anchor="e", width=LEFT_W)
        self.vol_label_left.grid(row=1, column=0, padx=(0, PAD), sticky="e")

        self.volume_slider = tk.Scale(
            sliders, from_=0, to=100, orient=tk.HORIZONTAL, length=SLIDER_LENGTH,
            resolution=1, bg=BG, fg=FG, troughcolor=ACCENT,
            highlightthickness=0, showvalue=0, command=self.on_volume_change
        )
        self.volume_slider.set(int(MASTER_VOLUME))
        self.volume_slider.grid(row=1, column=1, sticky="w")

        self.vol_value = ttk.Label(sliders, text=f"{int(MASTER_VOLUME)}%", anchor="w", width=RIGHT_W)
        self.vol_value.grid(row=1, column=2, padx=(PAD, 0), sticky="w")

        # ---- Strike Floor row (0â€“100% -> 0.00â€“1.00)
        # Use a custom width so the full text is right-aligned next to the slider
        self.strike_label_left = ttk.Label(
            sliders, text="Strike Floor", anchor="e", width=LEFT_W
        )
        self.strike_label_left.grid(row=2, column=0, padx=(0, PAD), sticky="e")

        self.strike_slider = tk.Scale(
            sliders, from_=0, to=100, orient=tk.HORIZONTAL, length=SLIDER_LENGTH,
            resolution=1, bg=BG, fg=FG, troughcolor=ACCENT,
            highlightthickness=0, showvalue=0, command=self.on_strike_floor_change
        )
        self.strike_slider.set(int(MIN_STRIKE_FRAC * 100))
        self.strike_slider.grid(row=2, column=1, sticky="w")

        self.strike_value = ttk.Label(sliders, text=f"{int(MIN_STRIKE_FRAC * 100)}%", anchor="w", width=RIGHT_W)
        self.strike_value.grid(row=2, column=2, padx=(PAD, 0), sticky="w")



        # Centered title above the queue
        self.queue_title = ttk.Label(right, text="Playback Queue")
        self.queue_title.pack(anchor="center", pady=(0,6))

        # Queue list + scrollbars (compact height, full width)
        queue_list_frame = ttk.Frame(right)
        queue_list_frame.pack(fill="x", pady=(0,0))

        # use grid inside this frame so we can place both scrollbars
        queue_list_frame.grid_columnconfigure(0, weight=1)
        queue_list_frame.grid_rowconfigure(0, weight=1)

        self.queue_listbox = tk.Listbox(
            queue_list_frame,
            bg=PANEL, fg=FG,
            selectbackground=SEL_BG, selectforeground=FG,
            highlightthickness=0, bd=0, relief="flat",
            activestyle="none",
            height=2
        )
        self.queue_listbox.grid(row=0, column=0, sticky="nsew")  # fills available width

        # vertical scrollbar
        queue_vsb = ttk.Scrollbar(queue_list_frame, orient=tk.VERTICAL, command=self.queue_listbox.yview)
        queue_vsb.grid(row=0, column=1, sticky="ns")

        # Remove controls under the queue
        rm_wrap = ttk.Frame(right)
        rm_wrap.pack(pady=(6,0))

        rm_all = ttk.Button(rm_wrap, text="Remove All", command=self.remove_all)
        rm_all.pack(side=tk.LEFT, padx=6)

        rm_sel = ttk.Button(rm_wrap, text="Remove Selected", command=self.remove_selected)
        rm_sel.pack(side=tk.LEFT, padx=(6,4))

        # Up/down buttons (use proper Unicode arrows)
        self.move_up_btn = ttk.Button(rm_wrap, text="\u2191", width=2, command=self.move_selected_up)
        self.move_up_btn.pack(side=tk.LEFT, padx=2)

        self.move_down_btn = ttk.Button(rm_wrap, text="\u2193", width=2, command=self.move_selected_down)
        self.move_down_btn.pack(side=tk.LEFT, padx=2)

        # Keep arrow state updated whenever selection or queue changes
        self.queue_listbox.bind("<<ListboxSelect>>", self._update_move_buttons)

        # Initialize state
        self._update_move_buttons()

        # Toggles under remove buttons
        toggles = ttk.Frame(right)
        toggles.pack(pady=(6,0))

        # Load persisted states from config
        cfg = _read_config()
        self.solenoids_enabled = tk.BooleanVar(value=cfg.get("solenoids_enabled", True))
        self.rush_mode_enabled = tk.BooleanVar(value=cfg.get("rush_mode_enabled", False))
        self.loop_enabled = tk.BooleanVar(value=cfg.get("loop_enabled", False))
        self.shuffle_enabled = tk.BooleanVar(value=cfg.get("shuffle_enabled", False))
        self.audio_enabled = tk.BooleanVar(value=cfg.get("audio_enabled", True))

        solenoids_cb = tk.Checkbutton(
            toggles, text="Solenoids", variable=self.solenoids_enabled,
            bg=BG, fg=FG, selectcolor=ACCENT, cursor="arrow",
            command=self.on_solenoids_toggle
        )
        solenoids_cb.pack(side=tk.LEFT, padx=6)

        rush_cb = tk.Checkbutton(
            toggles, text="Rush Mode", variable=self.rush_mode_enabled,
            bg=BG, fg=FG, selectcolor=ACCENT, cursor="arrow",
            command=self.on_rush_mode_toggle
        )
        rush_cb.pack(side=tk.LEFT, padx=6)

        loop_cb = tk.Checkbutton(
            toggles, text="Loop", variable=self.loop_enabled,
            bg=BG, fg=FG, selectcolor=ACCENT, cursor="arrow",
            command=self.on_loop_toggle
        )
        loop_cb.pack(side=tk.LEFT, padx=6)

        shuffle_cb = tk.Checkbutton(
            toggles, text="Shuffle", variable=self.shuffle_enabled,
            bg=BG, fg=FG, selectcolor=ACCENT, cursor="arrow",
            command=self.on_shuffle_toggle
        )
        shuffle_cb.pack(side=tk.LEFT, padx=6)

        audio_cb = tk.Checkbutton(
            toggles, text="Audio", variable=self.audio_enabled,
            bg=BG, fg=FG, selectcolor=ACCENT, cursor="arrow",
            command=self.on_audio_toggle
        )
        audio_cb.pack(side=tk.LEFT, padx=6)


        # -------- HDMI Volume Boost (pactl, compact) --------
        self._audio_boost_updating = False
        self._audio_boost_after = None

        audio_boost_frame = ttk.Frame(right)
        audio_boost_frame.pack(anchor="center", pady=(6, 0))

        boost_row = ttk.Frame(audio_boost_frame)
        boost_row.pack(anchor="center")

        ttk.Label(boost_row, text="HDMI Volume", anchor="e", width=LEFT_W).pack(side=tk.LEFT, padx=(0, PAD))

        self.audio_boost_slider = tk.Scale(
            boost_row,
            from_=0,
            to=AUDIO_BOOST_MAX_VOLUME,
            orient=tk.HORIZONTAL,
            length=SLIDER_LENGTH,
            resolution=AUDIO_BOOST_STEP,
            bg=BG,
            fg=FG,
            troughcolor=ACCENT,
            highlightthickness=0,
            showvalue=0,
            command=self.on_audio_boost_change,
        )
        self.audio_boost_slider.set(100)
        self.audio_boost_slider.pack(side=tk.LEFT)

        self.audio_boost_value = ttk.Label(boost_row, text="100%", anchor="w", width=RIGHT_W)
        self.audio_boost_value.pack(side=tk.LEFT, padx=(PAD, 0))

        boost_buttons = ttk.Frame(audio_boost_frame)
        boost_buttons.pack(anchor="center", pady=(2, 0))

        for boost_value in (100, 150, 200, 300, 400):
            ttk.Button(
                boost_buttons,
                text=f"{boost_value}%",
                width=5,
                command=lambda v=boost_value: self.set_audio_boost_volume(v),
            ).pack(side=tk.LEFT, padx=2)

        ttk.Button(boost_buttons, text="Mute", width=6, command=self.mute_audio_boost).pack(side=tk.LEFT, padx=(8, 2))
        ttk.Button(boost_buttons, text="Refresh", width=7, command=self.refresh_audio_boost_volume).pack(side=tk.LEFT, padx=2)

        # No HDMI volume status label here.
        # The current value is already shown to the right of the slider.

        self.after(900, self.refresh_audio_boost_volume)
        self.after(2500, self.periodic_audio_boost_refresh)
        # -----------------------------------------------------

        # -------- LED Light Controls (compact, 2-column) --------
        led_frame = ttk.Frame(right)
        led_frame.pack(anchor="center", pady=(4,0))

        ttk.Label(led_frame, text="LED Light Controls").grid(row=0, column=0, columnspan=2, pady=(0,2))

        # two columns inside the LED section
        left_col  = ttk.Frame(led_frame)
        right_col = ttk.Frame(led_frame)
        left_col.grid(row=1, column=0, sticky="nw")
        right_col.grid(row=1, column=1, sticky="ne", padx=(8,0))

        # helper: compact horizontal scale with a label on the left
        def _mk_scale(parent, label, key, length=150):
            row = parent.grid_size()[1]  # next available row
            ttk.Label(parent, text=label).grid(row=row, column=0, padx=(0,4), sticky="e")
            sc = tk.Scale(
                parent, from_=0, to=100, orient=tk.HORIZONTAL, length=length,
                bg=BG, fg=FG, troughcolor=ACCENT, highlightthickness=0, showvalue=0,
                command=lambda _v, k=key: self.on_led_slider_change(k, int(float(_v)))
            )
            sc.set(int(_led_cfg.get(key, 100)))
            sc.grid(row=row, column=1, sticky="w", pady=1)
            return sc

        # LEFT COLUMN: Brightness (renamed) then Effect
        self.brightness_slider = _mk_scale(left_col, "Brightness", "brightness")

        ttk.Label(left_col, text="Effect").grid(row=left_col.grid_size()[1], column=0, padx=(0,4), sticky="e")
        self.led_effect_var = tk.StringVar(value=_led_cfg.get("effect", "Solid"))
        effects_options = ["Solid", "RGB", "Random RGB", "Rainbow Effect", "Moving Rainbow", "Dancing", "Flicker", "Christmas", "Track"]
        eff = ttk.Combobox(
            left_col,
            textvariable=self.led_effect_var,
            values=effects_options,
            state="readonly",
            width=14,
            style="LED.TCombobox"
        )
        eff.grid(row=left_col.grid_size()[1]-1, column=1, sticky="w", pady=(2,0))  # same row as Effect label
        eff.bind("<<ComboboxSelected>>", self.on_effect_change)

        # Idle Effect dropdown
        ttk.Label(left_col, text="Idle Effect").grid(
            row=left_col.grid_size()[1], column=0, padx=(0,4), sticky="e"
        )
        self.idle_effect_var = tk.StringVar(value=_led_cfg.get("idle_effect", "Off"))
        idle_effects_options = ["Off", "Solid", "R->L Rainbow", "L->R Rainbow", "Rainbow", "RGB Cable", "RGB Cable Gaps", "4th of July", "Flicker", "Christmas"]
        idle_cb = ttk.Combobox(
            left_col,
            textvariable=self.idle_effect_var,
            values=idle_effects_options,
            state="readonly",
            width=14,
            style="LED.TCombobox"
        )
        idle_cb.grid(row=left_col.grid_size()[1]-1, column=1, sticky="w", pady=(2,0))
        idle_cb.bind("<<ComboboxSelected>>", self.on_idle_effect_change)

        
        # NEW: Idle Speed slider
        ttk.Label(left_col, text="Idle Speed").grid(row=left_col.grid_size()[1], column=0, padx=(0,4), sticky="e")
        self.idle_speed_slider = tk.Scale(
            left_col, from_=1, to=100, orient=tk.HORIZONTAL, length=150,
            bg=BG, fg=FG, troughcolor=ACCENT, highlightthickness=0, showvalue=0,
            command=lambda v: self.on_led_slider_change("speed", int(float(v)))
        )
        self.idle_speed_slider.set(int(_led_cfg.get("speed", 20)))
        self.idle_speed_slider.grid(row=left_col.grid_size()[1]-1, column=1, sticky="w", pady=(2,0))


        # RIGHT COLUMN: Red, Green, Blue, Favorite
        self.red_slider   = _mk_scale(right_col, "Red",   "red")
        self.green_slider = _mk_scale(right_col, "Green", "green")
        self.blue_slider  = _mk_scale(right_col, "Blue",  "blue")

        # Favorite button:
        #   short press = play the saved favorite song
        #   hold 5 seconds while a song is selected = save that song as the favorite
        fav_row = right_col.grid_size()[1]
        self.favorite_btn = ttk.Button(right_col, text="Favorite", width=18)
        self.favorite_btn.grid(row=fav_row, column=0, columnspan=2, sticky="ew", pady=(6, 0))
        self.version_label = ttk.Label(right_col, text=f"v{APP_VERSION}", anchor="e", font=("TkDefaultFont", 8))
        self.version_label.grid(row=fav_row, column=2, sticky="se", padx=(8, 0), pady=(8, 0))
        self.favorite_btn.bind("<ButtonPress-1>", self._favorite_button_press)
        self.favorite_btn.bind("<ButtonRelease-1>", self._favorite_button_release)
        self.update_favorite_button_label()
        # ------------------------------------------------
        # Load songs
        self.songs_folder = MIDI_DIR
        self.all_songs = self._scan_folder(self.songs_folder)
        self.filtered_songs = list(self.all_songs)
        self.update_song_listbox(self.filtered_songs)

        # ---- Watchdog: auto-refresh Songs when files change ----
        self._watchdog_job = None
        self._observer = Observer()
        self._observer.daemon = True
        self._observer_handler = SongFolderHandler(self)
        self._observer.schedule(self._observer_handler, self.songs_folder, recursive=True)
        self._observer.start()




        # start LED worker
        self.led_worker.start()
        # Paint the idle LEDs immediately at startup. No ten-second darkness tax.
        _request_led_render()

        self.after(200, self.update_scrubber)  # periodic slider update
        if not REAL_PIANO:
            self.after(1, self.poll_recording_midi_input)
        self.after(700, self._ensure_auto_windows_for_current_song)  # open idle visualizer + mixer
        self.protocol("WM_DELETE_WINDOW", self.on_close)

    def _update_visualizer_for_current_song(self):
        """Start the persistent visualizer if needed, then send it the current song/filter/position."""
        try:
            viz = getattr(self, "_viz", None)
            if not viz or not viz.top.winfo_exists():
                self._viz = VisualizerWindow(self)
            else:
                viz.update_from_gui()
        except Exception as e:
            print("[Visualizer] update failed:", e)

    def _queue_live_visualizer_update(self, delay_ms: int = 1):
        """Batch live-key visualizer updates. Kept for cleanup/expiry paths."""
        try:
            if getattr(self, "_live_visual_update_after", None):
                return

            def _do_update():
                self._live_visual_update_after = None
                self._update_visualizer_for_current_song()

            self._live_visual_update_after = self.after(max(1, int(delay_ms)), _do_update)
        except Exception:
            try:
                self._update_visualizer_for_current_song()
            except Exception:
                pass

    def _flush_live_visualizer_update(self):
        """Push live-key state to the visualizer immediately.

        The separate visualizer process reads a small state file each frame.
        Waiting 16 ms here made quick repeated key presses feel mushy, so live
        keyboard hits bypass the debounce. The computer can survive one tiny
        JSON write per key event. Probably.
        """
        try:
            job = getattr(self, "_live_visual_update_after", None)
            if job:
                try:
                    self.after_cancel(job)
                except Exception:
                    pass
                self._live_visual_update_after = None
            self._update_visualizer_for_current_song()
        except Exception:
            pass

    # ---------- Song list helpers (search / update) ----------
    def _scan_folder(self, folder):
        if not os.path.isdir(folder):
            print(f"[WARN] Songs folder not found: {folder}")
            self._song_path_by_display = {}
            return []

        found = []
        for root_dir, _dirs, files in os.walk(folder):
            for name in files:
                if name.lower().endswith((".mid", ".midi")):
                    full_path = os.path.join(root_dir, name)
                    stem = os.path.splitext(name)[0]
                    rel_no_ext = os.path.splitext(os.path.relpath(full_path, folder))[0].replace(os.sep, "/")
                    found.append((stem, rel_no_ext, full_path))

        # Prefer clean stems in the UI. If two files have the same stem, show the relative path.
        counts = {}
        for stem, _rel, _path in found:
            counts[stem] = counts.get(stem, 0) + 1

        display_to_path = {}
        display_names = []
        for stem, rel, path in sorted(found, key=lambda x: (x[0].lower(), x[1].lower())):
            display = stem if counts.get(stem, 0) == 1 else rel
            display_to_path[display] = path
            display_names.append(display)

        self._song_path_by_display = display_to_path
        return display_names

    def update_song_listbox(self, songs):
        self.file_listbox.delete(0, tk.END)
        for s in songs:
            self.file_listbox.insert(tk.END, s)

    def search_songs(self, _event=None):
        q = self.search_entry.get().strip().lower()
        if not q:
            self.filtered_songs = list(self.all_songs)
        else:
            self.filtered_songs = [s for s in self.all_songs if q in s.lower()]
        self.update_song_listbox(self.filtered_songs)

    # ---------- Queue controls ----------
    def add_selected(self):
        sel = self.file_listbox.curselection()
        if not sel:
            return
        full_path = self._song_path_for_display_name(self.file_listbox.get(sel[0]))
        if not full_path:
            return
        self.queue_files.append(full_path)
        self.refresh_queue()

        if self.currently_playing is None:
            self.play_next()

    def _selected_song_display_and_path(self):
        sel = self.file_listbox.curselection()
        if not sel:
            return None, None
        display = self.file_listbox.get(sel[0])
        path = self._song_path_for_display_name(display)
        return display, path

    def _show_rename_dialog(self, old_name: str):
        dialog = tk.Toplevel(self)
        dialog.title("Rename Song")
        dialog.resizable(False, False)
        dialog.transient(self)
        dialog.grab_set()

        outer = ttk.Frame(dialog, padding=14)
        outer.pack(fill=tk.BOTH, expand=True)

        ttk.Label(outer, text="New song name:", font=("TkDefaultFont", 12, "bold")).pack(anchor="w")
        name_var = tk.StringVar(value=old_name)
        entry = ttk.Entry(outer, textvariable=name_var, style="Search.TEntry", width=34)
        entry.pack(fill=tk.X, pady=(8, 12))

        result = {"value": None}

        def close_keyboard_and_focus_out():
            try:
                _set_touchscreen_keyboard_visible(False)
                dialog.focus_set()
            except Exception:
                pass

        def accept(_event=None):
            result["value"] = name_var.get()
            close_keyboard_and_focus_out()
            dialog.destroy()

        def cancel(_event=None):
            result["value"] = None
            close_keyboard_and_focus_out()
            dialog.destroy()

        buttons = ttk.Frame(outer)
        buttons.pack(fill=tk.X)
        ttk.Button(buttons, text="Cancel", command=cancel).pack(side=tk.RIGHT, padx=(6, 0))
        ttk.Button(buttons, text="Rename", command=accept).pack(side=tk.RIGHT)

        entry.bind("<FocusIn>", lambda _e: _set_touchscreen_keyboard_visible(True), add="+")
        entry.bind("<FocusOut>", lambda _e: _set_touchscreen_keyboard_visible(False), add="+")
        entry.bind("<Return>", accept, add="+")
        entry.bind("<Escape>", cancel, add="+")

        def _hide_osk_if_click_outside_entry(event):
            try:
                if event.widget is entry:
                    return
                dialog.after_idle(close_keyboard_and_focus_out)
            except Exception:
                pass

        dialog.bind("<Button-1>", _hide_osk_if_click_outside_entry, add="+")

        try:
            dialog.update_idletasks()
            w = max(420, dialog.winfo_reqwidth())
            h = max(150, dialog.winfo_reqheight())
            x = self.winfo_rootx() + max(0, (self.winfo_width() - w) // 2)
            y = self.winfo_rooty() + 70
            dialog.geometry(f"{w}x{h}+{x}+{y}")
        except Exception:
            pass

        entry.focus_set()
        entry.selection_range(0, tk.END)
        self.wait_window(dialog)
        return result["value"]

    def rename_selected_song(self):
        display, old_path = self._selected_song_display_and_path()
        if not old_path or not os.path.exists(old_path):
            messagebox.showinfo("Rename", "Select a song to rename first.")
            return

        folder = os.path.dirname(old_path)
        old_stem, ext = os.path.splitext(os.path.basename(old_path))
        proposed = self._show_rename_dialog(old_stem)
        if proposed is None:
            return

        new_stem = os.path.splitext(os.path.basename(str(proposed).strip()))[0].strip()
        new_stem = new_stem.replace("/", "_").replace("\\", "_")
        if not new_stem:
            messagebox.showwarning("Rename", "Type a valid song name.")
            return

        new_path = os.path.join(folder, new_stem + (ext or ".mid"))
        if _safe_abs(new_path) == _safe_abs(old_path):
            return
        if os.path.exists(new_path):
            messagebox.showwarning("Rename", f"A file named {os.path.basename(new_path)} already exists.")
            return

        try:
            was_playing = self.currently_playing and _safe_abs(self.currently_playing) == _safe_abs(old_path)
            if was_playing:
                self.stop_current()

            os.rename(old_path, new_path)
            if _is_keyboard_recording_path(old_path):
                _move_keyboard_recording_metadata(old_path, new_path)
            _move_instrument_filter_key(old_path, new_path)

            if _safe_abs(getattr(self, "favorite_song_path", "")) == _safe_abs(old_path):
                self.favorite_song_path = new_path
                _cfg["favorite_song"] = new_path
                _write_config(_cfg)
                self._update_favorite_button_label()

            self.queue_files = [new_path if _safe_abs(p) == _safe_abs(old_path) else p for p in self.queue_files]
            self.refresh_queue()
            self.refresh_song_list()
            self._select_song_path_in_list(new_path)
            self.status.config(text=f"Renamed: {os.path.basename(new_path)}")
        except Exception as e:
            messagebox.showerror("Rename", f"Could not rename song:\n{e}")

    def delete_selected_song(self):
        display, path = self._selected_song_display_and_path()
        if not path or not os.path.exists(path):
            messagebox.showinfo("Delete", "Select a song to delete first.")
            return

        name = os.path.basename(path)
        ok = messagebox.askyesno(
            "Delete Song",
            f"Delete this song from disk?\n\n{name}\n\nThis cannot be undone.",
            parent=self,
        )
        if not ok:
            return

        try:
            if self.currently_playing and _safe_abs(self.currently_playing) == _safe_abs(path):
                self.stop_current()

            os.remove(path)
            if _is_keyboard_recording_path(path):
                _delete_keyboard_recording_metadata(path)
            _delete_instrument_filter_key(path)

            if _safe_abs(getattr(self, "favorite_song_path", "")) == _safe_abs(path):
                self.favorite_song_path = ""
                _cfg["favorite_song"] = ""
                _write_config(_cfg)
                self._update_favorite_button_label()

            self.queue_files = [p for p in self.queue_files if _safe_abs(p) != _safe_abs(path)]
            self.refresh_queue()
            self.refresh_song_list()
            self.status.config(text=f"Deleted: {name}")
        except Exception as e:
            messagebox.showerror("Delete", f"Could not delete song:\n{e}")

    def refresh_song_list(self):
        """Rescan folder, reapply current search filter, and preserve selection when possible."""
        sel_name = None
        sel = self.file_listbox.curselection()
        if sel:
            sel_name = self.file_listbox.get(sel[0])

        self.all_songs = self._scan_folder(self.songs_folder)
        self.search_songs()  # uses whatever is typed in Search box

        if sel_name and sel_name in self.filtered_songs:
            idx = self.filtered_songs.index(sel_name)
            self.file_listbox.selection_set(idx)
            self.file_listbox.see(idx)

    def schedule_watchdog_refresh(self):
        """Debounce rapid sequences of FS events."""
        if getattr(self, "_watchdog_job", None):
            self.after_cancel(self._watchdog_job)
        self._watchdog_job = self.after(300, self.refresh_song_list)



    # ---------- Live keyboard LEDs / idle interruption ----------
    def _program_is_idle_for_live_keyboard(self) -> bool:
        return (not self.currently_playing) and (not self.recording)

    def _idle_effect_suspended(self) -> bool:
        try:
            if self.recording:
                return True
            return time.time() < float(getattr(self, "idle_effect_pause_until", 0.0))
        except Exception:
            return False

    def _mark_live_keyboard_activity(self):
        # Extend the idle pause, but do not cancel/reschedule a Tk timer for
        # every MIDI byte. That was wasting time exactly when quick playing
        # needs the UI to be responsive. Tiny scheduling taxes add up.
        self.idle_effect_pause_until = time.time() + 10.0
        try:
            if getattr(self, "_idle_resume_after", None) is None:
                self._idle_resume_after = self.after(10050, self._resume_idle_effect_if_due)
        except Exception:
            pass

    def _resume_idle_effect_if_due(self):
        try:
            self._idle_resume_after = None
            remaining = float(getattr(self, "idle_effect_pause_until", 0.0)) - time.time()
            if remaining > 0:
                self._idle_resume_after = self.after(max(25, int(remaining * 1000) + 50), self._resume_idle_effect_if_due)
                return
            if self.currently_playing is None and not self.recording:
                self._clear_live_keyboard_visuals()
                _request_led_render()
        except Exception:
            pass

    def _clear_live_keyboard_visuals(self):
        try:
            self.live_keyboard_active_notes.clear()
            self.live_keyboard_held_notes.clear()
            self.live_keyboard_note_expiry.clear()
        except Exception:
            pass
        try:
            if self.currently_playing is None:
                _clear_active_midi_notes()
                _try_update_led_strip_now(self)
        except Exception:
            pass
        try:
            self._flush_live_visualizer_update()
        except Exception:
            pass

    def _expire_live_keyboard_note(self, note: int):
        try:
            note = int(note)
            if note in getattr(self, "live_keyboard_held_notes", set()):
                return
            until = float(getattr(self, "live_keyboard_note_expiry", {}).get(note, 0.0))
            if time.time() < until:
                delay_ms = max(25, int(round((until - time.time()) * 1000)))
                self.after(delay_ms, lambda n=note: self._expire_live_keyboard_note(n))
                return
            self.live_keyboard_note_expiry.pop(note, None)
            self.live_keyboard_active_notes.pop(note, None)
            if self.currently_playing is None:
                _deactivate_midi_note(note, None)
                _try_update_led_strip_now(self)
            self._flush_live_visualizer_update()
        except Exception:
            pass

    def _schedule_live_keyboard_note_expiry(self, note: int, hold_ms: int = 25):
        try:
            note = int(note)
            self.live_keyboard_note_expiry[note] = time.time() + max(0.015, hold_ms / 1000.0)
            self.after(max(15, int(hold_ms) + 5), lambda n=note: self._expire_live_keyboard_note(n))
        except Exception:
            pass

    def _handle_live_keyboard_visuals(self, msg):
        """Light the screen/LEDs from live keyboard input without forwarding sound."""
        try:
            if msg.type == "note_on" and getattr(msg, "velocity", 0) > 0:
                note = int(msg.note)
                velocity = int(getattr(msg, "velocity", 100))
                if FIRST_NOTE <= note <= LAST_NOTE:
                    self.live_keyboard_held_notes.add(note)
                    self.live_keyboard_active_notes[note] = velocity
                    # Cancel any pending expiry so repeated same-key presses
                    # re-arm cleanly instead of feeling glued on.
                    self.live_keyboard_note_expiry.pop(note, None)
                    _activate_midi_note(note, None)
                    _try_update_led_strip_now(self)
                    self._flush_live_visualizer_update()
            elif msg.type == "note_off" or (msg.type == "note_on" and getattr(msg, "velocity", 0) == 0):
                note = int(msg.note)
                self.live_keyboard_held_notes.discard(note)
                if FIRST_NOTE <= note <= LAST_NOTE:
                    # End the live effect on release. The visualizer still draws
                    # particles for a moment, but the held-note bar/key lighting
                    # stops with the actual key release.
                    self.live_keyboard_note_expiry.pop(note, None)
                    self.live_keyboard_active_notes.pop(note, None)
                    _deactivate_midi_note(note, None)
                    _try_update_led_strip_now(self)
                    self._flush_live_visualizer_update()
        except Exception:
            pass

    # ---------- Keyboard recording ----------
    def _preferred_recording_input_name(self):
        try:
            inputs = mido.get_input_names()
        except Exception as e:
            self.status.config(text=f"MIDI input error: {e}")
            return None

        if not inputs:
            return None

        for needle in ("recital", "alesis", "midi"):
            match = next((name for name in inputs if needle in name.lower()), None)
            if match:
                return match
        return inputs[0]

    def _open_recording_input(self, quiet: bool = False):
        if self.recording_midi_in_port is not None:
            return True

        name = self._preferred_recording_input_name()
        if not name:
            if not quiet:
                messagebox.showerror("Record", "No MIDI input ports were found.")
            return False

        try:
            self.recording_midi_in_port = mido.open_input(name)
            self.recording_input_name = name
            # Drain anything already queued when the port opens so startup does
            # not blank the idle effects for ten seconds. MIDI devices apparently
            # enjoy saying hello with old crumbs from their pockets.
            try:
                for _ in self.recording_midi_in_port.iter_pending():
                    pass
                self.idle_effect_pause_until = 0.0
            except Exception:
                pass
            return True
        except Exception as e:
            if not quiet:
                messagebox.showerror("Record", f"Could not open MIDI input:\n{name}\n\n{e}")
            self.recording_midi_in_port = None
            return False

    def _close_recording_input(self):
        if self.recording_midi_in_port is not None:
            try:
                self.recording_midi_in_port.close()
            except Exception:
                pass
            self.recording_midi_in_port = None

    def _set_recording_buttons(self):
        try:
            if self.record_btn is not None:
                self.record_btn.configure(
                    state=tk.NORMAL,
                    style=("RecordActive.TButton" if self.recording else "Compact.TButton"),
                    text=("REC" if self.recording else "Rec"),
                )
            # Stop Rec was merged into the Rec toggle button. Keep this guard so
            # old attributes remain harmless if a previous layout created them.
            if self.stop_record_btn is not None:
                self.stop_record_btn.configure(state=tk.DISABLED)
            if self.save_recording_btn is not None:
                can_save = (not self.recording) and bool(self.recording_events)
                self.save_recording_btn.configure(state=(tk.NORMAL if can_save else tk.DISABLED))
        except Exception:
            pass

    def toggle_keyboard_recording(self):
        if REAL_PIANO:
            return
        if self.recording:
            self.stop_keyboard_recording()
        else:
            self.start_keyboard_recording()

    def start_keyboard_recording(self):
        if REAL_PIANO:
            return
        if self.recording:
            return

        # Recording should be a deliberate act, not an accidental duet with the queue.
        if self.currently_playing is not None:
            self.stop_current(continue_queue=False)

        if not self._open_recording_input():
            return

        # Flush old pending messages so the recording starts when the user presses Record.
        try:
            for _ in self.recording_midi_in_port.iter_pending():
                pass
        except Exception:
            pass

        self.recording_events = []
        self.recording_active_notes = {}
        self.current_recording_path = None
        self.recording_program = DEFAULT_RECORDING_PROGRAM
        self.recording_start = time.monotonic()
        self.recording = True
        self._set_recording_buttons()
        self.status.config(text=f"Recording from {self.recording_input_name}...")

    def stop_keyboard_recording(self):
        if not self.recording:
            return

        # Close any keys still being held so the saved MIDI does not hang forever.
        try:
            elapsed = max(0.0, time.monotonic() - float(self.recording_start or time.monotonic()))
            for channel, note in sorted(getattr(self, "recording_active_notes", {}).keys()):
                self.recording_events.append((elapsed, mido.Message("note_off", channel=channel, note=note, velocity=0, time=0)))
            self.recording_active_notes.clear()
        except Exception:
            pass

        self.recording = False
        # Keep the input open after recording so idle keyboard LEDs still work.
        self._set_recording_buttons()
        self.status.config(text=f"Recording stopped ({len(self.recording_events)} MIDI messages)")

    def _recording_msg_for_file(self, msg):
        # Ignore timing/system chatter. Capture notes, sustain pedal CC, bends, program changes, etc.
        if getattr(msg, "is_meta", False):
            return None
        if msg.type in ("clock", "start", "stop", "continue", "active_sensing", "reset"):
            return None

        try:
            if msg.type == "note_on" and getattr(msg, "velocity", 0) == 0:
                return mido.Message(
                    "note_off",
                    channel=getattr(msg, "channel", 0),
                    note=int(msg.note),
                    velocity=0,
                    time=0,
                )
            clean = msg.copy(time=0)
            return clean
        except Exception:
            return None

    def poll_recording_midi_input(self):
        try:
            # In keyboard hardware mode, keep one MIDI input open all the time.
            # It drives idle LEDs/screen lighting, and recording just saves those
            # same incoming messages. No live notes are forwarded to MIDI output
            # or FluidSynth, because feedback loops are not music.
            if self.recording_midi_in_port is None:
                now_try = time.monotonic()
                if now_try - float(getattr(self, "_last_recording_input_open_attempt", 0.0)) >= 2.0:
                    self._last_recording_input_open_attempt = now_try
                    self._open_recording_input(quiet=True)

            if self.recording_midi_in_port is not None:
                any_visual_change = False
                now_mono = time.monotonic()

                for raw_msg in self.recording_midi_in_port.iter_pending():
                    msg = self._recording_msg_for_file(raw_msg)
                    if msg is None:
                        continue

                    self._mark_live_keyboard_activity()

                    if self.currently_playing is None:
                        self._handle_live_keyboard_visuals(msg)
                        any_visual_change = True

                    if self.recording:
                        elapsed = max(0.0, now_mono - float(self.recording_start or now_mono))
                        self.recording_events.append((elapsed, msg))

                        try:
                            if msg.type == "note_on" and getattr(msg, "velocity", 0) > 0:
                                self.recording_active_notes[(getattr(msg, "channel", 0), int(msg.note))] = True
                            elif msg.type == "note_off" or (msg.type == "note_on" and getattr(msg, "velocity", 0) == 0):
                                self.recording_active_notes.pop((getattr(msg, "channel", 0), int(msg.note)), None)
                        except Exception:
                            pass

                if any_visual_change:
                    _request_led_render()

        except Exception as e:
            self.recording = False
            self._close_recording_input()
            self._set_recording_buttons()
            self.status.config(text=f"Recording input disconnected: {e}")

        try:
            self.after(1, self.poll_recording_midi_input)
        except Exception:
            pass

    def _write_keyboard_recording_midi(self, path, events, program):
        program = max(0, min(127, int(program)))
        mid = mido.MidiFile(type=0, ticks_per_beat=TICKS_PER_BEAT)
        track = mido.MidiTrack()
        mid.tracks.append(track)
        track.append(mido.MetaMessage("set_tempo", tempo=DEFAULT_TEMPO, time=0))
        track.append(mido.Message("program_change", channel=0, program=program, time=0))

        previous_time = 0.0
        for event_time, msg in events:
            try:
                # The user-selected instrument wins. Input program changes can go sit in the corner.
                if msg.type == "program_change":
                    continue

                event_time = float(event_time)
                delta_seconds = max(0.0, event_time - previous_time)
                previous_time = event_time
                delta_ticks = int(round(mido.second2tick(
                    delta_seconds,
                    ticks_per_beat=TICKS_PER_BEAT,
                    tempo=DEFAULT_TEMPO,
                )))
                out_msg = msg.copy(time=delta_ticks)
                track.append(out_msg)
            except Exception:
                continue

        track.append(mido.MetaMessage("end_of_track", time=0))
        mid.save(path)

    def save_keyboard_recording(self):
        if REAL_PIANO:
            return
        if self.recording:
            self.stop_keyboard_recording()
        if not self.recording_events:
            messagebox.showinfo("Save Recording", "There is no recording to save yet.")
            return

        os.makedirs(self.recordings_folder, exist_ok=True)
        suggested = f"KR{time.strftime('%Y%m%d_%H%M%S')}.mid"
        path = filedialog.asksaveasfilename(
            parent=self,
            title="Save Keyboard Recording",
            initialdir=self.recordings_folder,
            initialfile=suggested,
            defaultextension=".mid",
            filetypes=[("MIDI files", "*.mid"), ("MIDI files", "*.midi"), ("All files", "*.*")],
        )
        if not path:
            return
        if not path.lower().endswith((".mid", ".midi")):
            path += ".mid"

        try:
            os.makedirs(os.path.dirname(path), exist_ok=True)
            self._write_keyboard_recording_midi(path, self.recording_events, self.recording_program)

            _update_keyboard_recording_metadata(
                path,
                created_at=time.strftime("%Y-%m-%d %H:%M:%S"),
                input=self.recording_input_name,
                event_count=len(self.recording_events),
                instrument=int(self.recording_program),
                instrument_name=GENERAL_MIDI_PROGRAMS[int(self.recording_program)],
            )

            # For keyboard recordings, default to both piano/test-rig and speaker playback.
            try:
                save_instrument_settings_for_song(
                    path,
                    piano_indices=[0],
                    speaker_indices=[0],
                    filter_audio=True,
                    piano_volume_scales={0: 100},
                )
            except Exception as e:
                print(f"[WARN] Could not save default recording instrument routing: {e}")

            self.current_recording_path = path
            self.refresh_song_list()
            self._select_song_path_in_list(path)
            self.status.config(text=f"Saved keyboard recording: {os.path.basename(path)}")
            self.after(150, lambda p=path: self.open_instrument_mixer(song_path=p, auto=True))
        except Exception as e:
            messagebox.showerror("Save Recording", f"Could not save MIDI recording:\n{e}")

    def _select_song_path_in_list(self, path):
        try:
            target = _safe_abs(path)
            for idx, display in enumerate(self.filtered_songs):
                mapped = self._song_path_for_display_name(display)
                if mapped and _safe_abs(mapped) == target:
                    self.file_listbox.selection_clear(0, tk.END)
                    self.file_listbox.selection_set(idx)
                    self.file_listbox.activate(idx)
                    self.file_listbox.see(idx)
                    return True
        except Exception:
            pass
        return False

    # ---------- Instrument mixer / track filtering ----------
    def _selected_or_current_song_path(self):
        if self.currently_playing:
            return self.currently_playing
        sel = self.file_listbox.curselection()
        if sel:
            return self._song_path_for_display_name(self.file_listbox.get(sel[0]))
        return None

    def _track_count_for_song(self, path):
        try:
            if not path:
                return int(_led_cfg.get("track_color_count", current_track_color_count))
            return max(1, len(get_midi_instrument_info(path)))
        except Exception:
            return int(_led_cfg.get("track_color_count", current_track_color_count))

    def _enabled_instrument_indices_for_song(self, path):
        try:
            return get_instrument_settings_for_song(path).get("enabled_indices", [])
        except Exception as e:
            print(f"[WARN] Could not load instrument filter for {path}: {e}")
            return None

    def _piano_volume_scales_for_song(self, path):
        try:
            return get_instrument_settings_for_song(path).get("piano_volume_scales", {})
        except Exception as e:
            print(f"[WARN] Could not load piano volume scales for {path}: {e}")
            return {}

    def _audio_instrument_indices_for_song(self, path):
        """Tracks FluidSynth should play, from the speaker column in the Instrument Mixer."""
        try:
            selected = self._enabled_instrument_indices_for_song(path)
            return get_audio_complement_indices_for_song(path, enabled_indices=selected)
        except Exception as e:
            print(f"[WARN] Could not compute speaker-only instrument filter for {path}: {e}")
            return None

    def _current_playback_offset(self) -> float:
        """Best estimate of where the song is right now, in seconds."""
        if self.currently_playing and self.playback_start_time is not None:
            try:
                if not self.playback_thread.is_paused() and not getattr(self, "scrub_dragging", False):
                    return max(0.0, min(float(self.current_duration or 0.0), time.time() - float(self.playback_start_time)))
            except Exception:
                pass
        try:
            return max(0.0, float(self.scrub_slider.get()))
        except Exception:
            return 0.0

    def _set_visualizer_clock(self, offset: float):
        try:
            self._visualizer_playback_start_mono = time.monotonic() - max(0.0, float(offset))
        except Exception:
            self._visualizer_playback_start_mono = None

    def _clear_visualizer_clock(self):
        self._visualizer_playback_start_mono = None

    def _prepare_visualizer_for_physical_start(self, offset: float) -> int:
        """Freeze the visualizer until the solenoid scheduler actually starts."""
        try:
            self._playback_generation = int(getattr(self, "_playback_generation", 0)) + 1
        except Exception:
            self._playback_generation = 1
        self._visualizer_waiting_for_physical_start = True
        self._clear_visualizer_clock()
        try:
            self.scrub_slider.set(max(0.0, float(offset)))
        except Exception:
            pass
        self._update_visualizer_for_current_song()
        return int(self._playback_generation)

    def _make_physical_start_callback(self, path: str, generation: int):
        def _callback(start_offset: float, start_mono: float, start_wall: float, started_path: str = None):
            try:
                self.after(0, lambda: self._on_physical_playback_started(
                    path, generation, start_offset, start_mono, start_wall, started_path
                ))
            except Exception:
                pass
        return _callback

    def _on_physical_playback_started(self, path: str, generation: int, start_offset: float,
                                      start_mono: float, start_wall: float, started_path: str = None):
        try:
            if int(generation) != int(getattr(self, "_playback_generation", 0)):
                return
            if not self.currently_playing or os.path.abspath(str(self.currently_playing)) != os.path.abspath(str(path)):
                return
            if started_path and os.path.abspath(str(started_path)) != os.path.abspath(str(path)):
                return
            offset = max(0.0, float(start_offset))
            self._start_deferred_audio_if_ready(path, offset)
            self.playback_start_time = float(start_wall) - offset
            self._visualizer_playback_start_mono = float(start_mono) - offset
            self._visualizer_waiting_for_physical_start = False
            try:
                self.scrub_slider.set(offset)
            except Exception:
                pass
            self._update_visualizer_for_current_song()
        except Exception as e:
            print(f"[WARN] Could not sync visualizer to physical playback start: {e}")

    def _start_fluidsynth_process(self, play_path, temp_audio_file=None, filter_audio_mode=None):
        """Start FluidSynth for an already-prepared MIDI path."""
        if self.audio_process is not None:
            try:
                self.audio_process.kill()
            except Exception:
                pass
            self.audio_process = None

        self._cleanup_temp_audio()
        if temp_audio_file:
            self.temp_audio_file = temp_audio_file

        try:
            self.audio_process = subprocess.Popen(
                ["fluidsynth", "-a", "pulseaudio", "-i", SOUND_FONT, play_path],
                stdout=subprocess.DEVNULL,
                stderr=subprocess.DEVNULL,
            )
            self._current_audio_filter_audio = filter_audio_mode
        except Exception as e:
            print(f"[WARN] Could not start fluidsynth: {e}")

    def _prepare_fluidsynth_playback(self, midi_path, start_offset: float = 0.0):
        """Prepare the MIDI path FluidSynth should play, without starting audio yet."""
        audio_indices = self._audio_instrument_indices_for_song(midi_path)

        if audio_indices is not None and len(audio_indices) == 0:
            return {"play_path": None, "temp_path": None, "filter_audio_mode": "unchecked"}

        play_path = midi_path
        temp_path = None
        if audio_indices is not None:
            tmp = trim_midi_file_custom(midi_path, start_offset, instrument_indices=audio_indices)
            if tmp:
                temp_path = tmp
                play_path = tmp
        elif start_offset > 0.0:
            tmp = trim_midi_file_custom(midi_path, start_offset, instrument_indices=None)
            if tmp:
                temp_path = tmp
                play_path = tmp

        return {"play_path": play_path, "temp_path": temp_path, "filter_audio_mode": "unchecked"}

    def _start_prepared_fluidsynth(self, prepared):
        """Start FluidSynth from a prepared audio payload."""
        if not prepared or not prepared.get("play_path"):
            if self.audio_process is not None:
                try:
                    self.audio_process.kill()
                except Exception:
                    pass
                self.audio_process = None
            self._cleanup_temp_audio()
            self._current_audio_filter_audio = "unchecked"
            return
        self._start_fluidsynth_process(
            prepared.get("play_path"),
            temp_audio_file=prepared.get("temp_path"),
            filter_audio_mode=prepared.get("filter_audio_mode", "unchecked"),
        )

    def _prepare_deferred_audio_start(self, midi_path, start_offset: float = 0.0):
        """Prepare speaker audio now, but launch it when the physical scheduler arms."""
        self._deferred_audio_start = None
        if self.audio_process is not None:
            try:
                self.audio_process.kill()
            except Exception:
                pass
            self.audio_process = None
        self._cleanup_temp_audio()
        if not self.audio_enabled.get():
            return
        prepared = self._prepare_fluidsynth_playback(midi_path, start_offset)
        self._deferred_audio_start = {
            "path": os.path.abspath(str(midi_path)),
            "offset": float(start_offset),
            "prepared": prepared,
        }

    def _start_deferred_audio_if_ready(self, midi_path, start_offset: float = 0.0):
        prepared_entry = getattr(self, "_deferred_audio_start", None)
        if not prepared_entry:
            return
        try:
            if os.path.abspath(str(midi_path)) != prepared_entry.get("path"):
                return
        except Exception:
            return
        self._deferred_audio_start = None
        self._start_prepared_fluidsynth(prepared_entry.get("prepared"))

    def _start_fluidsynth_for_path(self, midi_path, start_offset: float = 0.0):
        """Start FluidSynth with only the tracks assigned to the Speakers column."""
        self._start_prepared_fluidsynth(self._prepare_fluidsynth_playback(midi_path, start_offset))

    def _rush_mode_on(self) -> bool:
        try:
            return bool(self.rush_mode_enabled.get())
        except Exception:
            return False

    def _restart_current_song_at_offset(self, offset=None):
        """Immediate restart helper used by seek/legacy paths."""
        if not self.currently_playing:
            return
        if offset is None:
            offset = self._current_playback_offset()

        selected = self._enabled_instrument_indices_for_song(self.currently_playing)
        piano_volume_scales = self._piano_volume_scales_for_song(self.currently_playing)

        # Prepare speaker audio now, but launch it when the physical scheduler arms.
        self._prepare_deferred_audio_start(self.currently_playing, start_offset=offset)

        generation = self._prepare_visualizer_for_physical_start(offset)
        self.playback_thread.seek(
            self.currently_playing,
            offset,
            self._playback_done,
            instrument_indices=selected,
            piano_volume_scales=piano_volume_scales,
            started_callback=self._make_physical_start_callback(self.currently_playing, generation),
            rush_mode=self._rush_mode_on(),
        )
        cut_all_solenoids_and_clear()
        _clear_active_midi_notes()
        _clear_leds()

        self._update_visualizer_for_current_song()

    def _apply_live_piano_filter(self, song_path, cut_notes: bool = False):
        """Apply Piano-column/volume mixer changes to the running scheduler immediately."""
        try:
            if not self.currently_playing or os.path.abspath(self.currently_playing) != os.path.abspath(song_path):
                return
            selected = self._enabled_instrument_indices_for_song(song_path)
            piano_volume_scales = self._piano_volume_scales_for_song(song_path)
            self.playback_thread.update_filter(selected, piano_volume_scales)

            # If the set of tracks changed, cut anything currently held so disabled
            # tracks cannot keep a solenoid down until their old note_off arrives.
            # A tiny cut is vastly better than freezing the whole song for a rebuild.
            if cut_notes:
                cut_all_solenoids_and_clear()
                _clear_active_midi_notes()
                _request_led_render()

            self._update_visualizer_for_current_song()
        except Exception as e:
            print(f"[WARN] Could not apply live piano filter: {e}")

    def _defer_paused_instrument_switch(self, song_path, prepared_audio_path=None):
        """Remember mixer changes made while paused and keep every clock frozen.

        Restarting the physical scheduler while paused creates the classic bad
        split-brain: solenoids stay paused but the visualizer thinks it got a
        new clock and starts moving. So paused mixer edits are applied visually
        right now, then the physical/audio restart happens on Resume at the
        current scrub position.
        """
        if prepared_audio_path and os.path.exists(prepared_audio_path):
            try:
                os.remove(prepared_audio_path)
            except Exception:
                pass
        try:
            selected = self._enabled_instrument_indices_for_song(song_path)
            piano_volume_scales = self._piano_volume_scales_for_song(song_path)
            self.playback_thread.update_filter(selected, piano_volume_scales)
        except Exception:
            pass
        self._pending_paused_instrument_restart = True
        self._pending_paused_instrument_song = os.path.abspath(str(song_path))
        try:
            cut_all_solenoids_and_clear()
            _clear_active_midi_notes()
            _clear_leds()
        except Exception:
            pass
        self._visualizer_waiting_for_physical_start = False
        # Keep the current paused offset frozen. Do not reset the visualizer clock.
        self._update_visualizer_for_current_song()
        try:
            self.status.config(text="Instrument changes saved; will apply to playback when resumed.")
        except Exception:
            pass

    def _schedule_instrument_filter_switch(self, song_path, debounce_ms: int = 150, restart_physical: bool = False):
        """
        Apply instrument changes without freezing the mixer.

        The old playback keeps running while any replacement MIDI audio is prepared.
        If audio must be swapped, the new audio file is prepared for a short future
        target offset, then solenoids/audio/visualizer are switched together when
        the song reaches that offset.
        """
        self._instrument_change_job_id = int(getattr(self, "_instrument_change_job_id", 0)) + 1
        job_id = self._instrument_change_job_id

        old_after = getattr(self, "_pending_instrument_change_after", None)
        if old_after:
            try:
                self.after_cancel(old_after)
            except Exception:
                pass

        def begin():
            self._pending_instrument_change_after = None
            self._begin_instrument_filter_switch(song_path, job_id, restart_physical=restart_physical)

        self._pending_instrument_change_after = self.after(debounce_ms, begin)

    def _begin_instrument_filter_switch(self, song_path, job_id: int, lead_seconds: float = 0.75, retry_count: int = 0, restart_physical: bool = False):
        if job_id != getattr(self, "_instrument_change_job_id", 0):
            return

        # If the edited song is not currently playing, saving the JSON is enough.
        if not self.currently_playing or os.path.abspath(self.currently_playing) != os.path.abspath(song_path):
            return

        try:
            is_paused_now = bool(self.playback_thread.is_paused())
        except Exception:
            is_paused_now = False
        if is_paused_now:
            self._defer_paused_instrument_switch(song_path)
            return

        current_offset = self._current_playback_offset()
        target_offset = min(float(self.current_duration or current_offset), current_offset + lead_seconds)

        # Near the end, just switch now. There is not enough runway to stage a new file.
        if target_offset <= current_offset + 0.05:
            self._commit_instrument_filter_switch(job_id, song_path, current_offset, None, needs_audio_swap=True, restart_physical=restart_physical)
            return

        # Always prepare speaker audio from the complement of the checked tracks.
        # This prevents FluidSynth from doubling whatever the physical piano is playing.
        audio_indices = self._audio_instrument_indices_for_song(song_path)

        # If no speaker tracks remain, no temp MIDI is needed. We will stop FluidSynth
        # at the splice point and let the piano play alone.
        if not self.audio_enabled.get() or (audio_indices is not None and len(audio_indices) == 0):
            delay_ms = max(0, int((target_offset - current_offset) * 1000))
            self.status.config(text="Instrument filter queued; speaker audio will be updated at the splice point.")
            self.after(delay_ms, lambda: self._commit_instrument_filter_switch(job_id, song_path, target_offset, None, needs_audio_swap=True, restart_physical=restart_physical))
            return

        self.status.config(text="Preparing speaker-only MIDI in background...")

        def worker():
            tmp = None
            try:
                tmp = trim_midi_file_custom(song_path, target_offset, instrument_indices=audio_indices)
            except Exception as e:
                print(f"[WARN] Could not prepare speaker-only MIDI: {e}")
            self.after(0, lambda: self._finish_prepared_instrument_switch(job_id, song_path, target_offset, tmp, retry_count, restart_physical=restart_physical))

        threading.Thread(target=worker, daemon=True).start()

    def _finish_prepared_instrument_switch(self, job_id: int, song_path, target_offset: float, tmp_path, retry_count: int, restart_physical: bool = False):
        if job_id != getattr(self, "_instrument_change_job_id", 0) or not self.currently_playing or os.path.abspath(self.currently_playing) != os.path.abspath(song_path):
            if tmp_path and os.path.exists(tmp_path):
                try:
                    os.remove(tmp_path)
                except Exception:
                    pass
            return

        current_offset = self._current_playback_offset()
        time_until_target = target_offset - current_offset

        # If preparation missed the target, try again farther in the future.
        if time_until_target < 0.12 and retry_count < 3:
            if tmp_path and os.path.exists(tmp_path):
                try:
                    os.remove(tmp_path)
                except Exception:
                    pass
            self._begin_instrument_filter_switch(song_path, job_id, lead_seconds=0.75, retry_count=retry_count + 1, restart_physical=restart_physical)
            return

        delay_ms = max(0, int(time_until_target * 1000))
        self.status.config(text="Speaker-only MIDI ready; splicing instruments...")
        self.after(delay_ms, lambda: self._commit_instrument_filter_switch(job_id, song_path, target_offset, tmp_path, needs_audio_swap=True, restart_physical=restart_physical))

    def _commit_instrument_filter_switch(self, job_id: int, song_path, offset: float, prepared_audio_path, needs_audio_swap: bool, restart_physical: bool = False):
        if job_id != getattr(self, "_instrument_change_job_id", 0):
            if prepared_audio_path and os.path.exists(prepared_audio_path):
                try:
                    os.remove(prepared_audio_path)
                except Exception:
                    pass
            return
        if not self.currently_playing or os.path.abspath(self.currently_playing) != os.path.abspath(song_path):
            if prepared_audio_path and os.path.exists(prepared_audio_path):
                try:
                    os.remove(prepared_audio_path)
                except Exception:
                    pass
            return

        try:
            is_paused_now = bool(self.playback_thread.is_paused())
        except Exception:
            is_paused_now = False
        if is_paused_now:
            self._defer_paused_instrument_switch(song_path, prepared_audio_path=prepared_audio_path)
            return

        selected = self._enabled_instrument_indices_for_song(song_path)
        piano_volume_scales = self._piano_volume_scales_for_song(song_path)
        offset = max(0.0, min(float(self.current_duration or offset), float(offset)))

        # Kill/replace FluidSynth at the same splice point as the solenoid event stream.
        # It is not sample-perfect because FluidSynth is being relaunched as a process,
        # but the speakers no longer contain the selected piano tracks, so small launch
        # latency no longer produces doubled piano notes.
        if self.audio_enabled.get() and needs_audio_swap:
            audio_indices = self._audio_instrument_indices_for_song(song_path)
            if audio_indices is not None and len(audio_indices) == 0:
                if self.audio_process is not None:
                    try:
                        self.audio_process.kill()
                    except Exception:
                        pass
                    self.audio_process = None
                self._cleanup_temp_audio()
                if prepared_audio_path and os.path.exists(prepared_audio_path):
                    try:
                        os.remove(prepared_audio_path)
                    except Exception:
                        pass
            elif prepared_audio_path:
                self._start_fluidsynth_process(prepared_audio_path, temp_audio_file=prepared_audio_path, filter_audio_mode="unchecked")
            else:
                self._start_fluidsynth_for_path(song_path, start_offset=offset)
        elif prepared_audio_path and os.path.exists(prepared_audio_path):
            try:
                os.remove(prepared_audio_path)
            except Exception:
                pass

        if restart_physical:
            generation = self._prepare_visualizer_for_physical_start(offset)
            self.playback_thread.seek(
                song_path,
                offset,
                self._playback_done,
                instrument_indices=selected,
                piano_volume_scales=piano_volume_scales,
                started_callback=self._make_physical_start_callback(song_path, generation),
                rush_mode=self._rush_mode_on(),
            )

            cut_all_solenoids_and_clear()
            _clear_active_midi_notes()
            _clear_leds()
        else:
            # Speaker-only updates do not need to restart the solenoid scheduler.
            # The Piano column is handled live through PlaybackControls.update_filter().
            self.playback_thread.update_filter(selected, piano_volume_scales)

        self._update_visualizer_for_current_song()

        enabled_count = len(selected or [])
        speaker_count = len(self._audio_instrument_indices_for_song(song_path) or [])
        self.status.config(text=f"Instrument filter active: piano {enabled_count} track(s), speakers {speaker_count} track(s)")


    def _close_instrument_mixer_window(self):
        win = getattr(self, "_instrument_mixer_win", None)
        try:
            self._instrument_mixer_win = None
            self._instrument_mixer_song_path = None
        except Exception:
            pass
        try:
            if win is not None and win.winfo_exists():
                win.destroy()
        except Exception:
            pass


    def _position_instrument_mixer_window(self, win):
        """Pin Instrument Mixer to the right of the player and keep it below the top taskbar."""
        try:
            if win is None or not win.winfo_exists():
                return

            self.update_idletasks()

            screen_w = int(self.winfo_screenwidth())
            screen_h = int(self.winfo_screenheight())

            # Use the player window's actual current geometry when possible.
            try:
                player_x = int(self.winfo_x())
                player_y = int(self.winfo_y())
                player_w = int(self.winfo_width())
                player_h = int(self.winfo_height())
            except Exception:
                player_x, player_y = 0, 30
                player_w = screen_w // 2
                player_h = max(300, screen_h // 2 - player_y)

            # Keep safely below the Pi top panel/taskbar.
            mixer_x = max(0, player_x + player_w)
            mixer_y = max(30, player_y)
            mixer_w = max(500, screen_w - mixer_x)
            mixer_h = max(260, player_h)

            win.geometry(f"{mixer_w}x{mixer_h}+{mixer_x}+{mixer_y}")
            win.minsize(500, 260)
        except Exception as exc:
            print(f"[WARN] Could not position Instrument Mixer: {exc}")


    def _prepare_instrument_mixer_window(self, song_path, title="Instrument Mixer"):
        """Create or reuse the Instrument Mixer window without closing/reopening it."""
        win = None
        try:
            existing = getattr(self, "_instrument_mixer_win", None)
            if existing is not None and existing.winfo_exists():
                win = existing
                for child in win.winfo_children():
                    try:
                        child.destroy()
                    except Exception:
                        pass
        except Exception:
            win = None

        if win is None:
            win = tk.Toplevel(self)
            win.protocol("WM_DELETE_WINDOW", self._close_instrument_mixer_window)

        self._instrument_mixer_win = win
        self._instrument_mixer_song_path = song_path
        win.title(title)

        # Same tiled layout as the player and visualizer.
        layout = _compute_app_window_layout(self)
        self._app_layout = layout
        mixer_x = layout["mixer_x"]
        mixer_y = layout["top_y"]
        mixer_w = layout["mixer_w"]
        mixer_h = layout["top_h"]

        try:
            win.geometry(f"{mixer_w}x{mixer_h}+{mixer_x}+{mixer_y}")
        except Exception:
            pass
        try:
            pass  # win.transient(self) disabled; it can let the window manager reposition the mixer
        except Exception:
            pass


        # Pin the mixer after creation and again after the WM has mapped it.
        # The repeated calls are intentional. Window managers are tiny chaos machines.
        try:
            self._position_instrument_mixer_window(win)
            self.after_idle(lambda w=win: self._position_instrument_mixer_window(w))
            self.after(250, lambda w=win: self._position_instrument_mixer_window(w))
            self.after(750, lambda w=win: self._position_instrument_mixer_window(w))
        except Exception:
            pass

        return win

    def _open_empty_instrument_mixer(self):
        """Open the instrument mixer before a song is selected/playing."""
        win = self._prepare_instrument_mixer_window(None, title="Instrument Mixer")

        outer = ttk.Frame(win, padding=18)
        outer.pack(fill=tk.BOTH, expand=True)
        ttk.Label(
            outer,
            text="Instrument Mixer",
            font=("TkDefaultFont", 14, "bold"),
        ).pack(anchor="w")
        ttk.Label(
            outer,
            text="No song is currently selected or playing.",
            font=("TkDefaultFont", 11),
        ).pack(anchor="w", pady=(14, 4))
        ttk.Label(
            outer,
            text="This window will update automatically when a song starts. The Piano column controls solenoids/LEDs/visualizer; the Speakers column controls FluidSynth.",
            wraplength=820,
        ).pack(anchor="w")
        ttk.Button(outer, text="Close", command=self._close_instrument_mixer_window).pack(anchor="e", pady=(24, 0))

    def open_instrument_mixer(self, song_path=None, auto=False):
        if song_path is None:
            song_path = self._selected_or_current_song_path()
        if not song_path:
            self._open_empty_instrument_mixer()
            return
        if not os.path.exists(song_path):
            messagebox.showerror("Instruments", f"MIDI file not found:\n{song_path}")
            return

        try:
            info = get_midi_instrument_info(song_path)
        except Exception as e:
            messagebox.showerror("Instruments", f"Could not read MIDI instruments:\n{e}")
            return

        if not info:
            messagebox.showinfo("Instruments", "No instruments/tracks were found in this MIDI file.")
            return

        settings = get_instrument_settings_for_song(song_path, info=info)
        piano_now = set(settings.get("piano_indices", settings.get("enabled_indices", [])))
        speaker_now = set(settings.get("speaker_indices", []))
        piano_volume_now = _normalize_piano_volume_scales(settings.get("piano_volume_scales", {}), info=info)

        win = self._prepare_instrument_mixer_window(song_path, title="Instrument Mixer")

        outer = ttk.Frame(win, padding=10)
        outer.pack(fill=tk.BOTH, expand=True)

        ttk.Label(
            outer,
            text=f"Instrument Mixer: {os.path.basename(song_path)}",
            font=("TkDefaultFont", 12, "bold"),
        ).pack(anchor="w")

        if _is_keyboard_recording_path(song_path):
            recording_tools = ttk.Frame(outer)
            recording_tools.pack(fill=tk.X, pady=(8, 6))
            ttk.Label(recording_tools, text="Recording Instrument:").pack(side=tk.LEFT, padx=(0, 6))

            meta = _get_keyboard_recording_metadata(song_path)
            try:
                current_program = int(meta.get("instrument", _first_program_in_midi(song_path, DEFAULT_RECORDING_PROGRAM)))
            except Exception:
                current_program = DEFAULT_RECORDING_PROGRAM
            current_program = max(0, min(127, current_program))

            instrument_values = [f"{i + 1:03d}  {name}" for i, name in enumerate(GENERAL_MIDI_PROGRAMS)]
            recording_inst_var = tk.StringVar(value=instrument_values[current_program])
            recording_inst_combo = ttk.Combobox(
                recording_tools,
                textvariable=recording_inst_var,
                values=instrument_values,
                state="readonly",
                width=34,
                style="LED.TCombobox",
            )
            recording_inst_combo.pack(side=tk.LEFT)

            def on_recording_instrument_change(_event=None):
                selected_text = recording_inst_var.get()
                try:
                    program = instrument_values.index(selected_text)
                except ValueError:
                    return
                try:
                    set_keyboard_recording_instrument(song_path, program)
                    self.recording_program = program
                    status_var.set(f"Recording instrument saved: {GENERAL_MIDI_PROGRAMS[program]}")
                    self.status.config(text=f"Recording instrument: {GENERAL_MIDI_PROGRAMS[program]}")
                    if self.currently_playing and os.path.abspath(self.currently_playing) == os.path.abspath(song_path):
                        self._restart_current_song_at_offset(self._current_playback_offset())
                except Exception as e:
                    messagebox.showerror("Recording Instrument", f"Could not update instrument:\n{e}")

            recording_inst_combo.bind("<<ComboboxSelected>>", on_recording_instrument_change)
            ttk.Label(
                recording_tools,
                text="Affects saved MIDI, FluidSynth speaker playback, and external MIDI playback.",
            ).pack(side=tk.LEFT, padx=(10, 0))

        ttk.Frame(outer, height=4).pack(fill=tk.X)

        status_var = tk.StringVar(value="Ready")
        try:
            mixer_bg = self.cget("bg")
        except Exception:
            mixer_bg = "#1e1e1e"
        canvas = tk.Canvas(outer, highlightthickness=0, bd=0, bg=mixer_bg)
        scroll = ttk.Scrollbar(outer, orient="vertical", command=canvas.yview)
        list_frame = ttk.Frame(canvas)
        list_window = canvas.create_window((0, 0), window=list_frame, anchor="nw")

        def _sync_scrollregion(_event=None):
            canvas.configure(scrollregion=canvas.bbox("all"))
            try:
                canvas.itemconfigure(list_window, width=canvas.winfo_width())
            except Exception:
                pass

        list_frame.bind("<Configure>", _sync_scrollregion)
        canvas.bind("<Configure>", _sync_scrollregion)
        canvas.configure(yscrollcommand=scroll.set)
        canvas.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        scroll.pack(side=tk.RIGHT, fill=tk.Y)

        piano_vars_by_idx = {}
        piano_volume_vars_by_idx = {}
        piano_volume_labels_by_idx = {}
        speaker_vars_by_idx = {}
        applying_programmatic_change = {"value": False}

        header_font = ("TkDefaultFont", 10, "bold")
        ttk.Label(list_frame, text="Piano", font=header_font).grid(row=0, column=0, sticky="w", padx=(0, 10), pady=(0, 4))
        ttk.Label(list_frame, text="Piano Vol", font=header_font).grid(row=0, column=1, sticky="w", padx=(0, 12), pady=(0, 4))
        ttk.Label(list_frame, text="Speakers", font=header_font).grid(row=0, column=2, sticky="w", padx=(0, 12), pady=(0, 4))
        ttk.Label(list_frame, text="Color", font=header_font).grid(row=0, column=3, sticky="w", padx=(0, 8), pady=(0, 4))
        ttk.Label(list_frame, text="Track / Instrument", font=header_font).grid(row=0, column=4, sticky="w", pady=(0, 4))

        def piano_indices():
            return [idx for idx, v in piano_vars_by_idx.items() if bool(v.get())]

        def speaker_indices():
            return [idx for idx, v in speaker_vars_by_idx.items() if bool(v.get())]

        def piano_volume_scales():
            return {idx: _clamp_percent(v.get(), 100) for idx, v in piano_volume_vars_by_idx.items()}

        last_saved = {
            "piano": set(piano_now),
            "speakers": set(speaker_now),
            "scales": dict(piano_volume_now),
        }

        def save_and_queue_change(*_args):
            # Debounced, so clicking several boxes does not restart the song several times.
            if applying_programmatic_change["value"]:
                return
            piano_selected = piano_indices()
            speaker_selected = speaker_indices()
            scale_selected = piano_volume_scales()
            piano_set = set(piano_selected)
            speaker_set = set(speaker_selected)
            piano_tracks_changed = piano_set != set(last_saved.get("piano", set()))
            piano_changed = piano_tracks_changed or scale_selected != dict(last_saved.get("scales", {}))
            speaker_changed = speaker_set != set(last_saved.get("speakers", set()))

            save_instrument_settings_for_song(
                song_path,
                piano_selected,
                speaker_selected,
                filter_audio=True,
                piano_volume_scales=scale_selected,
            )
            last_saved["piano"] = set(piano_set)
            last_saved["speakers"] = set(speaker_set)
            last_saved["scales"] = dict(scale_selected)

            overlap = sorted(set(piano_selected) & set(speaker_selected))
            msg = f"Saved: piano {len(piano_selected)} track(s), speakers {len(speaker_selected)} track(s)"
            if overlap:
                msg += f"; {len(overlap)} doubled"
            status_var.set(msg)
            self.status.config(text=f"Instrument filter saved: piano {len(piano_selected)}, speakers {len(speaker_selected)}")
            if self.currently_playing and os.path.abspath(self.currently_playing) == os.path.abspath(song_path):
                if piano_tracks_changed:
                    # The physical timeline is now built from the selected Piano tracks.
                    # Removing/volume tweaks can be live, but adding a newly selected track
                    # needs a quick synced rebuild so those notes actually exist in the
                    # running scheduler. Otherwise we are back to pretending checkboxes
                    # are magic spells. They are not.
                    self._apply_live_piano_filter(song_path, cut_notes=True)
                    self._schedule_instrument_filter_switch(song_path, debounce_ms=150, restart_physical=True)
                elif piano_changed:
                    self._apply_live_piano_filter(song_path, cut_notes=False)
                if speaker_changed and not piano_tracks_changed:
                    self._schedule_instrument_filter_switch(song_path, debounce_ms=150, restart_physical=False)

        def programmatic_update(fn):
            applying_programmatic_change["value"] = True
            try:
                fn()
            finally:
                applying_programmatic_change["value"] = False
            save_and_queue_change()

        for row, item in enumerate(info, start=1):
            idx = int(item["index"])
            piano_var = tk.BooleanVar(value=(idx in piano_now))
            speaker_var = tk.BooleanVar(value=(idx in speaker_now))
            piano_volume_var = tk.IntVar(value=_clamp_percent(piano_volume_now.get(idx, 100), 100))
            piano_vars_by_idx[idx] = piano_var
            speaker_vars_by_idx[idx] = speaker_var
            piano_volume_vars_by_idx[idx] = piano_volume_var

            label = (
                f"#{idx + 1:02d}  {item['name']}  |  {item['program_name']}"
                f"  |  notes: {item['note_count']}  |  range: {item['range']}"
            )
            if item.get("is_drum"):
                label += "  |  DRUMS"

            def _update_scale_label(value, _idx=idx):
                pct = _clamp_percent(value, 100)
                lbl = piano_volume_labels_by_idx.get(_idx)
                if lbl:
                    lbl.configure(text=f"{pct}%")

            ttk.Checkbutton(list_frame, variable=piano_var, command=save_and_queue_change).grid(row=row, column=0, sticky="w", padx=(0, 10), pady=2)

            vol_frame = ttk.Frame(list_frame)
            vol_frame.grid(row=row, column=1, sticky="w", padx=(0, 12), pady=2)
            vol_scale = ttk.Scale(vol_frame, from_=0, to=100, orient="horizontal", length=95, variable=piano_volume_var, command=_update_scale_label)
            vol_scale.pack(side=tk.LEFT)
            vol_label = ttk.Label(vol_frame, text=f"{_clamp_percent(piano_volume_var.get(), 100)}%", width=4, anchor="e")
            vol_label.pack(side=tk.LEFT, padx=(4, 0))
            piano_volume_labels_by_idx[idx] = vol_label
            vol_scale.bind("<ButtonRelease-1>", lambda _event, _idx=idx: save_and_queue_change())
            vol_scale.bind("<KeyRelease>", lambda _event, _idx=idx: save_and_queue_change())

            ttk.Checkbutton(list_frame, variable=speaker_var, command=save_and_queue_change).grid(row=row, column=2, sticky="w", padx=(0, 12), pady=2)
            track_rgb = track_color_for_index(idx, 1.0, len(info))
            track_hex = _rgb_to_hex(track_rgb)
            tk.Label(list_frame, text="  ", bg=track_hex, width=2, relief="flat").grid(row=row, column=3, sticky="w", padx=(0, 8), pady=2)
            tk.Label(list_frame, text=label, fg=track_hex, bg=mixer_bg, anchor="w").grid(row=row, column=4, sticky="w", pady=2)

        bottom = ttk.Frame(win, padding=(10, 6))
        bottom.pack(fill=tk.X)

        ttk.Label(bottom, textvariable=status_var).pack(side=tk.LEFT)

        def set_piano_all(value: bool):
            programmatic_update(lambda: [v.set(value) for v in piano_vars_by_idx.values()])

        def set_speakers_all(value: bool):
            programmatic_update(lambda: [v.set(value) for v in speaker_vars_by_idx.values()])

        def speakers_not_piano():
            def do_it():
                piano_set = set(piano_indices())
                for item in info:
                    idx = int(item["index"])
                    speaker_vars_by_idx[idx].set(item.get("note_count", 0) > 0 and idx not in piano_set)
            programmatic_update(do_it)

        def piano_only():
            def do_it():
                for item in info:
                    idx = int(item["index"])
                    is_piano = (not item["is_drum"]) and 0 <= int(item["program"]) <= 7 and item["note_count"] > 0
                    piano_vars_by_idx[idx].set(is_piano)
                # By default, speakers play everything that is not assigned to the piano.
                piano_set = {idx for idx, v in piano_vars_by_idx.items() if bool(v.get())}
                for item in info:
                    idx = int(item["index"])
                    speaker_vars_by_idx[idx].set(item.get("note_count", 0) > 0 and idx not in piano_set)
            programmatic_update(do_it)

        def melody_guess():
            def do_it():
                candidates = [x for x in info if x["note_count"] > 0 and not x["is_drum"]]
                if not candidates:
                    candidates = [x for x in info if x["note_count"] > 0]
                # Favor high average pitch and tracks that are not pure bass. Select the best two for the piano.
                ranked = sorted(candidates, key=lambda x: (x["avg_pitch"], x["max_pitch"], -x["note_count"]), reverse=True)
                chosen = {int(x["index"]) for x in ranked[:2]}
                for item in info:
                    idx = int(item["index"])
                    piano_vars_by_idx[idx].set(idx in chosen)
                    speaker_vars_by_idx[idx].set(item.get("note_count", 0) > 0 and idx not in chosen)
            programmatic_update(do_it)

        ttk.Button(bottom, text="Close", command=self._close_instrument_mixer_window).pack(side=tk.RIGHT, padx=3)
        ttk.Button(bottom, text="Piano All", command=lambda: set_piano_all(True)).pack(side=tk.RIGHT, padx=3)
        ttk.Button(bottom, text="Piano None", command=lambda: set_piano_all(False)).pack(side=tk.RIGHT, padx=3)
        ttk.Button(bottom, text="Speaker All", command=lambda: set_speakers_all(True)).pack(side=tk.RIGHT, padx=3)
        ttk.Button(bottom, text="Speaker None", command=lambda: set_speakers_all(False)).pack(side=tk.RIGHT, padx=3)
        ttk.Button(bottom, text="Speakers = Not Piano", command=speakers_not_piano).pack(side=tk.RIGHT, padx=3)
        ttk.Button(bottom, text="Piano Only", command=piano_only).pack(side=tk.RIGHT, padx=3)
        ttk.Button(bottom, text="Melody Guess", command=melody_guess).pack(side=tk.RIGHT, padx=3)

    def add_all_random(self):
        songs_to_add = list(self.file_listbox.get(0, tk.END))  # current (filtered) list
        if not songs_to_add:
            return
        random.shuffle(songs_to_add)
        for s in songs_to_add:
            full_path = self._song_path_for_display_name(s)
            if full_path:
                self.queue_files.append(full_path)
        self.refresh_queue()
        if self.currently_playing is None:
            self.play_next()

    def remove_all(self):
        self.queue_files.clear()
        self.refresh_queue()

    def remove_selected(self):
        sel = self.queue_listbox.curselection()
        if not sel:
            return
        idx = sel[0]
        if 0 <= idx < len(self.queue_files):
            del self.queue_files[idx]
        self.refresh_queue()

    def _update_move_buttons(self, *_):
        """Enable/disable up/down buttons based on selection position."""
        n = len(self.queue_files)
        sel = self.queue_listbox.curselection()
        if not sel or n == 0:
            self.move_up_btn.configure(state=tk.DISABLED)
            self.move_down_btn.configure(state=tk.DISABLED)
            return
        i = sel[0]
        self.move_up_btn.configure(state=(tk.NORMAL if i > 0 else tk.DISABLED))
        self.move_down_btn.configure(state=(tk.NORMAL if i < n - 1 else tk.DISABLED))

    def move_selected_up(self):
        sel = self.queue_listbox.curselection()
        if not sel:
            return
        i = sel[0]
        if i <= 0:
            return
        # swap in underlying list
        self.queue_files[i-1], self.queue_files[i] = self.queue_files[i], self.queue_files[i-1]
        self.refresh_queue()
        # restore selection & make sure itÃƒÆ’Ã†â€™Ãƒâ€ Ã¢â‚¬â„¢ÃƒÆ’Ã¢â‚¬Å¡Ãƒâ€šÃ‚Â¯ÃƒÆ’Ã†â€™ÃƒÂ¢Ã¢â€šÂ¬Ã…Â¡ÃƒÆ’Ã¢â‚¬Å¡Ãƒâ€šÃ‚Â¿ÃƒÆ’Ã†â€™ÃƒÂ¢Ã¢â€šÂ¬Ã…Â¡ÃƒÆ’Ã¢â‚¬Å¡Ãƒâ€šÃ‚Â½s visible
        self.queue_listbox.selection_set(i-1)
        self.queue_listbox.activate(i-1)
        self.queue_listbox.see(i-1)
        self._update_move_buttons()

    def move_selected_down(self):
        sel = self.queue_listbox.curselection()
        if not sel:
            return
        i = sel[0]
        if i >= len(self.queue_files) - 1:
            return
        self.queue_files[i+1], self.queue_files[i] = self.queue_files[i], self.queue_files[i+1]
        self.refresh_queue()
        self.queue_listbox.selection_set(i+1)
        self.queue_listbox.activate(i+1)
        self.queue_listbox.see(i+1)
        self._update_move_buttons()


    def refresh_queue(self):
        self.queue_listbox.delete(0, tk.END)
        for p in self.queue_files:
            base = os.path.splitext(os.path.basename(p))[0]
            self.queue_listbox.insert(tk.END, base)

    def _ensure_auto_windows_for_current_song(self):
        """Keep the visualizer and instrument mixer open.

        Before playback, both open as idle/placeholder windows. When a song starts,
        they rebuild/relaunch for that song. Humans call this convenience; window
        managers call it a negotiation.
        """
        if not self._auto_open_windows:
            return

        target_song = str(self.currently_playing) if self.currently_playing else None
        target_abs = os.path.abspath(target_song) if target_song else None

        # Visualizer: keep it open even before playback. Update it in place when the song changes.
        self._update_visualizer_for_current_song()

        # Instrument mixer: keep one window, and rebuild it when the current song changes.
        # When playback ends and there is no next song, currently_playing becomes None.
        # The old logic treated that as a song change and rebuilt the mixer into its
        # idle placeholder, which caused the end-of-song flash. Leave the existing
        # mixer alone until a real next song starts. Very advanced: don't repaint
        # a whole window just to announce "nothing." 
        try:
            mixer = getattr(self, "_instrument_mixer_win", None)
            mixer_alive = bool(mixer is not None and mixer.winfo_exists())
            mixer_song = getattr(self, "_instrument_mixer_song_path", None)
            mixer_abs = os.path.abspath(str(mixer_song)) if mixer_song else None

            if target_abs is None:
                if not mixer_alive:
                    self.open_instrument_mixer(song_path=None, auto=True)
                return

            if (not mixer_alive) or (mixer_abs != target_abs):
                self.open_instrument_mixer(song_path=self.currently_playing, auto=True)
        except Exception as e:
            print("[Instrument Mixer] auto-open failed:", e)

    def _apply_song_playback_settings_for_song(self, song_path):
        """Load saved per-song volume / strike floor. If none exist, keep current settings."""
        global MASTER_VOLUME, _MASTER_VOL_FRAC, MIN_STRIKE_FRAC

        settings = get_song_playback_settings_for_song(song_path)
        if not settings:
            return

        self._loading_song_playback_settings = True
        try:
            if "master_volume" in settings:
                MASTER_VOLUME = float(settings["master_volume"])
                _MASTER_VOL_FRAC = MIN_VOL_FRAC + (MASTER_VOLUME / 100.0) * (1.0 - MIN_VOL_FRAC)
                try:
                    self.volume_slider.set(int(MASTER_VOLUME))
                    self.vol_value.config(text=f"{int(MASTER_VOLUME)}%")
                except Exception:
                    pass

            if "min_strike_frac" in settings:
                MIN_STRIKE_FRAC = max(0.0, min(1.0, float(settings["min_strike_frac"])))
                pct = int(round(MIN_STRIKE_FRAC * 100))
                try:
                    self.strike_slider.set(pct)
                    self.strike_value.config(text=f"{pct}%")
                except Exception:
                    pass
        finally:
            self._loading_song_playback_settings = False

    def _save_current_song_playback_settings(self):
        """Persist current volume / strike floor for the currently playing MIDI file."""
        try:
            if self.currently_playing and not getattr(self, "_loading_song_playback_settings", False):
                save_song_playback_settings_for_song(
                    self.currently_playing,
                    master_volume=MASTER_VOLUME,
                    min_strike_frac=MIN_STRIKE_FRAC,
                )
        except Exception as e:
            print(f"[WARN] Could not save per-song playback settings: {e}")

    def _playback_done(self):
        self.after(0, self.on_song_complete)

    # ---------- Playback flow ----------
    def play_next(self):
        if not self.queue_files:
            self.currently_playing = None
            self.status.config(text="Currently Playing: (none)")
            self.scrub_slider.set(0)
            self.current_duration = 0.0
            self.playback_start_time = None
            self._visualizer_waiting_for_physical_start = False
            self.idle_effect_pause_until = 0.0
            self._clear_visualizer_clock()
            all_off()
            _clear_active_midi_notes()
            _clear_leds()
            _request_led_render()
            if self.audio_process is not None:
                try:
                    self.audio_process.kill()
                except Exception:
                    pass
                self.audio_process = None
            self._cleanup_temp_audio()
            self._update_visualizer_for_current_song()
            # Keep the secondary windows open; they drop back to idle placeholders.
            self.after(350, self._ensure_auto_windows_for_current_song)
            return

        if self.shuffle_enabled.get() and len(self.queue_files) > 1:
            idx = random.randrange(len(self.queue_files))
            next_file = self.queue_files.pop(idx)
        else:
            next_file = self.queue_files.pop(0)

        self.refresh_queue()

        self.currently_playing = next_file
        try:
            _set_current_track_color_count(self._track_count_for_song(next_file))
        except Exception:
            pass
        self.status.config(
            text=f"Currently Playing: {os.path.splitext(os.path.basename(next_file))[0]}"
        )
        try:
            self.play_history_logger.log_song_start(next_file, start_offset=0.0)
        except Exception as e:
            print(f"[WARN] Could not log song start: {e}")
        self._apply_song_playback_settings_for_song(next_file)
        global SOLENOIDS_PAUSED
        SOLENOIDS_PAUSED = not self.solenoids_enabled.get()
        if SOLENOIDS_PAUSED:
            cut_all_solenoids_and_clear()

        try:
            pm = _safe_pretty_midi(next_file)
            duration = pm.get_end_time()
        except Exception:
            duration = 0.0
        self.current_duration = duration
        self.scrub_slider.config(from_=0, to=max(0.1, duration), resolution=0.1)
        self.scrub_slider.set(0)

        selected = self._enabled_instrument_indices_for_song(next_file)
        piano_volume_scales = self._piano_volume_scales_for_song(next_file)

        # Prepare speaker audio now, but do not let it run ahead while the physical
        # event list is still being built. It starts when the solenoid scheduler arms.
        self._prepare_deferred_audio_start(next_file, start_offset=0.0)

        generation = self._prepare_visualizer_for_physical_start(0.0)
        self.playback_thread.play_file(
            next_file,
            start_offset=0.0,
            done_callback=self._playback_done,
            instrument_indices=selected,
            piano_volume_scales=piano_volume_scales,
            started_callback=self._make_physical_start_callback(next_file, generation),
            rush_mode=self._rush_mode_on(),
        )
        self.pause_btn.config(text="Pause")
        self.after(350, self._ensure_auto_windows_for_current_song)

    def on_song_complete(self):
        finished_song = self.currently_playing
        self.currently_playing = None
        if finished_song and self.loop_enabled.get():
            self.queue_files.append(finished_song)
            self.refresh_queue()
        self.play_next()

        self.after(350, self._ensure_auto_windows_for_current_song)

    def stop_current(self, continue_queue=True):
        global SOLENOIDS_PAUSED
        self.playback_thread.stop_current()
        SOLENOIDS_PAUSED = not self.solenoids_enabled.get()  # respect checkbox
        cut_all_solenoids_and_clear()
        _clear_active_midi_notes()
        _clear_leds()
        if self.audio_process is not None:
            try:
                self.audio_process.kill()
            except Exception:
                pass
            self.audio_process = None
        self._cleanup_temp_audio()
        self.currently_playing = None
        self.status.config(text="Currently Playing: (none)")
        self.scrub_slider.set(0)
        self.current_duration = 0.0
        self.playback_start_time = None
        self._visualizer_waiting_for_physical_start = False
        self.idle_effect_pause_until = 0.0
        self._clear_visualizer_clock()
        self._pause_wallclock = None
        _request_led_render()
        self._update_visualizer_for_current_song()
        if continue_queue:
            self.after(100, self.play_next)

    def toggle_pause(self):
        global SOLENOIDS_PAUSED
        if self.currently_playing is None:
            return
        if not self.playback_thread.is_paused():
            pause_offset = self._current_playback_offset()
            try:
                self.scrub_slider.set(pause_offset)
            except Exception:
                pass
            SOLENOIDS_PAUSED = True
            self.playback_thread.pause()
            self.pause_btn.config(text="Resume")
            self._pause_wallclock = time.time()
            cut_all_solenoids_and_clear()
            _clear_active_midi_notes()
            _clear_leds()
            if self.audio_enabled.get() and self.audio_process is not None:
                try:
                    os.kill(self.audio_process.pid, signal.SIGSTOP)
                except Exception:
                    pass
            self._update_visualizer_for_current_song()
        else:
            try:
                resume_offset = float(self.scrub_slider.get())
            except Exception:
                resume_offset = self._current_playback_offset()

            # If tracks changed while paused, restart from the paused scrub position
            # instead of resuming the old scheduler. This keeps visualizer, audio,
            # LEDs, and solenoids in one clock domain. Astonishing concept.
            pending_song = getattr(self, "_pending_paused_instrument_song", None)
            if getattr(self, "_pending_paused_instrument_restart", False) and self.currently_playing:
                try:
                    if pending_song and os.path.abspath(str(pending_song)) != os.path.abspath(str(self.currently_playing)):
                        pending_ok = False
                    else:
                        pending_ok = True
                except Exception:
                    pending_ok = True
                self._pending_paused_instrument_restart = False
                self._pending_paused_instrument_song = None
                if pending_ok:
                    self.pause_btn.config(text="Pause")
                    self._pause_wallclock = None
                    SOLENOIDS_PAUSED = not self.solenoids_enabled.get()
                    self._restart_current_song_at_offset(resume_offset)
                    return

            SOLENOIDS_PAUSED = not self.solenoids_enabled.get()  # respect checkbox
            self.playback_thread.resume()
            self.pause_btn.config(text="Pause")
            if self.playback_start_time is not None and self._pause_wallclock is not None:
                paused_span = time.time() - self._pause_wallclock
                self.playback_start_time += paused_span
            self._set_visualizer_clock(resume_offset)
            self._pause_wallclock = None
            if self.audio_enabled.get() and self.audio_process is not None:
                try:
                    os.kill(self.audio_process.pid, signal.SIGCONT)
                except Exception:
                    pass
            self._update_visualizer_for_current_song()


    # ---- Volume (remap 0ÃƒÆ’Ã†â€™Ãƒâ€ Ã¢â‚¬â„¢ÃƒÆ’Ã¢â‚¬Å¡Ãƒâ€šÃ‚Â¢ÃƒÆ’Ã†â€™Ãƒâ€šÃ‚Â¢ÃƒÆ’Ã‚Â¢ÃƒÂ¢Ã¢â‚¬Å¡Ã‚Â¬Ãƒâ€¦Ã‚Â¡ÃƒÆ’Ã¢â‚¬Å¡Ãƒâ€šÃ‚Â¬ÃƒÆ’Ã†â€™Ãƒâ€šÃ‚Â¢ÃƒÆ’Ã‚Â¢ÃƒÂ¢Ã¢â€šÂ¬Ã…Â¡Ãƒâ€šÃ‚Â¬ÃƒÆ’Ã¢â‚¬Â¦ÃƒÂ¢Ã¢â€šÂ¬Ã…â€œ100 ÃƒÆ’Ã†â€™Ãƒâ€ Ã¢â‚¬â„¢ÃƒÆ’Ã¢â‚¬Å¡Ãƒâ€šÃ‚Â¢ÃƒÆ’Ã†â€™Ãƒâ€šÃ‚Â¢ÃƒÆ’Ã‚Â¢ÃƒÂ¢Ã¢â€šÂ¬Ã…Â¡Ãƒâ€šÃ‚Â¬ÃƒÆ’Ã¢â‚¬Å¡Ãƒâ€šÃ‚Â ÃƒÆ’Ã†â€™Ãƒâ€šÃ‚Â¢ÃƒÆ’Ã‚Â¢ÃƒÂ¢Ã¢â€šÂ¬Ã…Â¡Ãƒâ€šÃ‚Â¬ÃƒÆ’Ã‚Â¢ÃƒÂ¢Ã¢â€šÂ¬Ã…Â¾Ãƒâ€šÃ‚Â¢ MIN_VOL_FRAC..1.0) + persist ----
    def on_volume_change(self, val):
        global MASTER_VOLUME, _MASTER_VOL_FRAC
        try:
            MASTER_VOLUME = float(val)
        except Exception:
            return
        _MASTER_VOL_FRAC = MIN_VOL_FRAC + (MASTER_VOLUME / 100.0) * (1.0 - MIN_VOL_FRAC)
        try:
            self.vol_value.config(text=f"{int(MASTER_VOLUME)}%")
        except Exception:
            pass

        if getattr(self, "_loading_song_playback_settings", False):
            return

        cfg = _read_config()
        cfg["master_volume"] = int(MASTER_VOLUME)
        cfg["rush_mode_enabled"] = bool(self.rush_mode_enabled.get())
        cfg["loop_enabled"] = bool(self.loop_enabled.get())
        cfg["shuffle_enabled"] = bool(self.shuffle_enabled.get())
        cfg["audio_enabled"] = bool(self.audio_enabled.get())
        _write_config(cfg)
        self._save_current_song_playback_settings()
        
        
    def on_strike_floor_change(self, val):
        global MIN_STRIKE_FRAC
        try:
            pct = int(float(val))
        except Exception:
            return
        # Clamp 0..100% and convert to 0.0..1.0
        pct = max(0, min(100, pct))
        MIN_STRIKE_FRAC = pct / 100.0
        try:
            self.strike_value.config(text=f"{pct}%")
        except Exception:
            pass

        if getattr(self, "_loading_song_playback_settings", False):
            return

        # Persist together with the other UI values
        cfg = _read_config()
        cfg["master_volume"] = int(MASTER_VOLUME)
        cfg["solenoids_enabled"] = bool(self.solenoids_enabled.get())
        cfg["rush_mode_enabled"] = bool(self.rush_mode_enabled.get())
        cfg["loop_enabled"] = bool(self.loop_enabled.get())
        cfg["shuffle_enabled"] = bool(self.shuffle_enabled.get())
        cfg["audio_enabled"] = bool(self.audio_enabled.get())
        cfg["min_strike_frac"] = float(MIN_STRIKE_FRAC)
        _write_config(cfg)
        self._save_current_song_playback_settings()


    # ---- Slider logic ----
    def on_slider_press(self, _event):
        self.scrub_dragging = True

    def on_slider_release(self, _event):
        if self.currently_playing and self.playback_start_time is not None:
            new_offset = float(self.scrub_slider.get())
            print(f"Seeking to {new_offset:.1f}s")
            selected = self._enabled_instrument_indices_for_song(self.currently_playing)
            piano_volume_scales = self._piano_volume_scales_for_song(self.currently_playing)

            self._prepare_deferred_audio_start(self.currently_playing, start_offset=new_offset)

            generation = self._prepare_visualizer_for_physical_start(new_offset)
            self.playback_thread.seek(
                self.currently_playing,
                new_offset,
                self._playback_done,
                instrument_indices=selected,
                piano_volume_scales=piano_volume_scales,
                started_callback=self._make_physical_start_callback(self.currently_playing, generation),
                rush_mode=self._rush_mode_on(),
            )

            # Keep the visualizer window open; it stays frozen until the physical scheduler starts.
            self._update_visualizer_for_current_song()
            self.after(350, self._ensure_auto_windows_for_current_song)
        self.scrub_dragging = False

    def update_scrubber(self):
        if (
            self.currently_playing
            and self.playback_start_time
            and not self.scrub_dragging
        ):
            if not self.playback_thread.is_paused():
                current_time = time.time() - self.playback_start_time
            else:
                # freeze time at pause
                current_time = self.scrub_slider.get()

            if current_time >= self.current_duration:
                current_time = self.current_duration
            self.scrub_slider.set(current_time)

            cur_mins, cur_secs = divmod(int(current_time), 60)
            dur_mins, dur_secs = divmod(int(self.current_duration), 60)

            self.current_time_label.config(text=f"{cur_mins}:{cur_secs:02d}")
            self.total_time_label.config(text=f"{dur_mins}:{dur_secs:02d}")
            try:
                viz = getattr(self, "_viz", None)
                if viz and viz.is_alive():
                    viz.update_from_gui()
            except Exception:
                pass
        else:
            # only reset if nothing is playing
            if not self.currently_playing:
                self.current_time_label.config(text="0:00")
                self.total_time_label.config(text="0:00")

        self.after(200, self.update_scrubber)




    # ----- HDMI / PipeWire / PulseAudio volume boost handlers -----
    def _set_audio_boost_status(self, text):
        # Status text intentionally hidden; the slider value already shows it.
        pass

    def _set_audio_boost_slider_display(self, volume):
        try:
            volume = int(round(float(volume)))
        except Exception:
            return

        shown = max(0, min(AUDIO_BOOST_MAX_VOLUME, volume))

        self._audio_boost_updating = True
        try:
            self.audio_boost_slider.set(shown)
            self.audio_boost_value.config(text=f"{volume}%")
        finally:
            self._audio_boost_updating = False

    def refresh_audio_boost_volume(self):
        try:
            volume = _audio_boost_get_sink_volume_percent()
            sink = _audio_boost_get_default_sink()
            self._set_audio_boost_slider_display(volume)
            self._set_audio_boost_status(f"System volume: {volume}%")
        except Exception as exc:
            self._set_audio_boost_status(f"Volume error: {exc}")

    def periodic_audio_boost_refresh(self):
        try:
            if getattr(self, "_audio_boost_after", None) is None:
                system_volume = _audio_boost_get_sink_volume_percent()
                slider_volume = int(round(float(self.audio_boost_slider.get())))
                if abs(system_volume - slider_volume) >= AUDIO_BOOST_STEP:
                    self._set_audio_boost_slider_display(system_volume)
        except Exception:
            pass

        try:
            self.after(2000, self.periodic_audio_boost_refresh)
        except Exception:
            pass

    def on_audio_boost_change(self, raw_value):
        if getattr(self, "_audio_boost_updating", False):
            return

        try:
            value = int(round(float(raw_value) / AUDIO_BOOST_STEP) * AUDIO_BOOST_STEP)
        except Exception:
            return

        value = max(0, min(AUDIO_BOOST_MAX_VOLUME, value))

        try:
            self.audio_boost_value.config(text=f"{value}%")
        except Exception:
            pass

        old_job = getattr(self, "_audio_boost_after", None)
        if old_job:
            try:
                self.after_cancel(old_job)
            except Exception:
                pass

        self._audio_boost_after = self.after(120, lambda v=value: self._apply_audio_boost_volume(v))

    def _apply_audio_boost_volume(self, value):
        self._audio_boost_after = None
        try:
            _audio_boost_set_sink_mute(False)
            _audio_boost_set_sink_volume_percent(value)
            self._set_audio_boost_status(f"System volume set to {int(value)}%")
        except Exception as exc:
            self._set_audio_boost_status(f"Volume error: {exc}")

    def set_audio_boost_volume(self, value):
        try:
            value = int(value)
        except Exception:
            return

        value = max(0, min(AUDIO_BOOST_MAX_VOLUME, value))

        try:
            self.audio_boost_slider.set(value)
        except Exception:
            pass

        self.on_audio_boost_change(value)

    def mute_audio_boost(self):
        try:
            _audio_boost_set_sink_mute(True)
            self._set_audio_boost_status("System audio muted")
        except Exception as exc:
            self._set_audio_boost_status(f"Volume error: {exc}")

    # ----- Favorite button handlers -----
    def _song_path_for_display_name(self, song_name: str) -> Optional[str]:
        """Return the real MIDI path for a display name from the song list."""
        song_name = str(song_name or "").strip()
        if not song_name:
            return None

        mapped = getattr(self, "_song_path_by_display", {}).get(song_name)
        if mapped:
            return mapped

        # Most files are .mid, but support .midi too, because naturally one
        # extension was not enough for civilization.
        for ext in (".mid", ".midi"):
            path = os.path.join(self.songs_folder, song_name + ext)
            if os.path.exists(path):
                return path

        # Fallback for existing behavior where .mid was assumed.
        return os.path.join(self.songs_folder, song_name + ".mid")

    def _selected_song_path_from_list(self) -> Optional[str]:
        try:
            sel = self.file_listbox.curselection()
            if not sel:
                return None
            return self._song_path_for_display_name(self.file_listbox.get(sel[0]))
        except Exception:
            return None

    def _favorite_button_text(self) -> str:
        """Return the button label: saved song name, or Favorite if none is saved."""
        song_path = str(getattr(self, "favorite_song_path", "") or "")
        if not song_path:
            return "Favorite"

        name = os.path.splitext(os.path.basename(song_path))[0].strip()
        if not name:
            return "Favorite"

        # Keep the control from exploding the right-side LED panel. The full
        # path stays saved; this is just the touch-button label.
        max_chars = 18
        if len(name) > max_chars:
            name = name[:max_chars - 3].rstrip() + "..."
        return name

    def update_favorite_button_label(self):
        try:
            self.favorite_btn.config(text=self._favorite_button_text())
        except Exception:
            pass

    def clear_favorite_song(self):
        self.favorite_song_path = ""
        cfg = _read_config()
        cfg["favorite_song"] = ""
        _write_config(cfg)
        self.update_favorite_button_label()

    def _favorite_button_press(self, _event=None):
        self._favorite_press_time = time.time()
        self._favorite_hold_fired = False

        if self._favorite_hold_after:
            try:
                self.after_cancel(self._favorite_hold_after)
            except Exception:
                pass
            self._favorite_hold_after = None

        self._favorite_hold_after = self.after(5000, self._favorite_button_long_hold)

    def _favorite_button_release(self, _event=None):
        if self._favorite_hold_after:
            try:
                self.after_cancel(self._favorite_hold_after)
            except Exception:
                pass
            self._favorite_hold_after = None

        # If the long-hold already saved the favorite, do not also play it.
        if self._favorite_hold_fired:
            self._favorite_press_time = None
            return

        self._favorite_press_time = None
        self.play_favorite_song()

    def _favorite_button_long_hold(self):
        self._favorite_hold_after = None
        self._favorite_hold_fired = True
        self.save_selected_song_as_favorite()

    def save_selected_song_as_favorite(self):
        song_path = self._selected_song_path_from_list()
        if not song_path:
            self.clear_favorite_song()
            self.status.config(text="Favorite cleared")
            return

        self.favorite_song_path = song_path
        cfg = _read_config()
        cfg["favorite_song"] = self.favorite_song_path
        _write_config(cfg)

        name = os.path.splitext(os.path.basename(song_path))[0]
        self.update_favorite_button_label()
        self.status.config(text=f"Favorite saved: {name}")

    def play_favorite_song(self):
        song_path = str(getattr(self, "favorite_song_path", "") or "")
        if not song_path:
            self.update_favorite_button_label()
            self.status.config(text="No favorite saved yet")
            return

        if not os.path.exists(song_path):
            self.update_favorite_button_label()
            self.status.config(text="Favorite song file not found")
            return

        # Play immediately: replace the queue with the favorite. If something is
        # playing, stop_current() will schedule play_next(), which will pick up
        # this queue entry. Tiny relay race, but it works.
        self.queue_files = [song_path]
        self.refresh_queue()

        if self.currently_playing is not None:
            self.stop_current()
        else:
            self.play_next()

    # ----- LED UI handlers -----
    def on_led_slider_change(self, key: str, value: int):
        _led_cfg[key] = int(value)
        _write_led_config(_led_cfg)
        _request_led_render()

    def on_effect_change(self, _evt=None):
        global current_led_effect
        current_led_effect = self.led_effect_var.get()
        _led_cfg["effect"] = current_led_effect
        _write_led_config(_led_cfg)
        _request_led_render()

    def on_idle_effect_change(self, _evt=None):
        global _led_cfg
        _led_cfg["idle_effect"] = self.idle_effect_var.get()
        _write_led_config(_led_cfg)
        _request_led_render()

    def _persist_config(self):
        cfg = {
            "master_volume": int(MASTER_VOLUME),
            "solenoids_enabled": bool(self.solenoids_enabled.get()),
            "rush_mode_enabled": bool(self.rush_mode_enabled.get()),
            "loop_enabled": bool(self.loop_enabled.get()),
            "shuffle_enabled": bool(self.shuffle_enabled.get()),
            "audio_enabled": bool(self.audio_enabled.get()),
            "min_strike_frac": float(MIN_STRIKE_FRAC),
            "favorite_song": str(getattr(self, "favorite_song_path", "") or "")
        }
        _write_config(cfg)
    
    def on_solenoids_toggle(self):
        global SOLENOIDS_PAUSED
        enabled = bool(self.solenoids_enabled.get())
        if not enabled:
            SOLENOIDS_PAUSED = True
            cut_all_solenoids_and_clear()
        else:
            SOLENOIDS_PAUSED = False
        self._persist_config()

    def on_rush_mode_toggle(self):
        self._persist_config()
        try:
            if self.currently_playing:
                mode = "on" if self._rush_mode_on() else "off"
                self.status.config(text=f"Rush Mode {mode}; restarting physical playback at current position...")
                self._restart_current_song_at_offset(self._current_playback_offset())
        except Exception as e:
            print(f"[WARN] Could not apply Rush Mode toggle: {e}")

    def on_loop_toggle(self):
        self._persist_config()

    def on_shuffle_toggle(self):
        self._persist_config()

    def on_audio_toggle(self):
        self._persist_config()

    def on_close(self):
        try:
            if getattr(self, "_viz", None) and self._viz and self._viz.top.winfo_exists():
                self._viz.close()
        except Exception:
            pass
        try:
            mixer = getattr(self, "_instrument_mixer_win", None)
            if mixer is not None and mixer.winfo_exists():
                mixer.destroy()
        except Exception:
            pass

        try:
            # persist current UI toggles/volume before shutdown
            try:
                self._persist_config()
            except Exception:
                pass

            cut_all_solenoids_and_clear()
            _clear_active_midi_notes()
            _clear_leds()
            if self.audio_process is not None:
                try:
                    self.audio_process.kill()
                except Exception:
                    pass
                self.audio_process = None
            self._cleanup_temp_audio()
            try:
                self._close_recording_input()
            except Exception:
                pass
        finally:
            try:
                self.play_history_logger.stop()
            except Exception:
                pass
            try:
                self.led_worker.stop()
            except Exception:
                pass
            try:
                pca0.deinit(); pca1.deinit(); pca2.deinit()
                pca3.deinit(); pca4.deinit(); pca5.deinit()
            except Exception:
                pass
            # Stop watchdog observer cleanly
            try:
                self._observer.stop()
                self._observer.join(timeout=1.0)
            except Exception:
                pass
            self.playback_thread.stop()
            self.destroy()

    
    def toggle_visualizer(self):
        # Open/close visualizer; remember its geometry
        if getattr(self, "_viz", None) and self._viz and self._viz.top.winfo_exists():
            try:
                self._viz.remember_geometry()
            except Exception:
                pass
            self._viz.close()
            self._viz = None
        else:
            try:
                self._viz = VisualizerWindow(self)
            except Exception as e:
                print("[Visualizer] failed to launch:", e)
    # --- helpers ---
    def _cleanup_temp_audio(self):
        if self.temp_audio_file and os.path.exists(self.temp_audio_file):
            try:
                os.remove(self.temp_audio_file)
            except Exception:
                pass
        self.temp_audio_file = None

# ----------------------------------------------------------------------
def _install_sig_handlers(app: MidiGUI):
    def _cleanup(signum, frame):
        try:
            app.on_close()
        finally:
            sys.exit(0)
    signal.signal(signal.SIGINT, _cleanup)
    signal.signal(signal.SIGTERM, _cleanup)

def main():
    global app
    if not os.path.isdir(MIDI_DIR):
        print(f"[WARN] Folder not found: {MIDI_DIR}")

    pb = PlaybackThread(); pb.start()
    app = MidiGUI(pb)
    attach_web_bridge(app)
    WebServer(port=8000).start()
    _install_sig_handlers(app)
    try:
        app.mainloop()
    except KeyboardInterrupt:
        pass
    finally:
        all_off()

# ======== BEGIN: Local Web UI (Flask) bridge ========
import queue
from flask import Flask, request, jsonify, Response

# Thread-safe command queue (web -> GUI) and state snapshot (GUI -> web)
_COMMANDS: "queue.Queue[tuple[str, dict]]" = queue.Queue()
_STATE = {}

def _enqueue(action: str, **args):
    _COMMANDS.put((action, args))

def attach_web_bridge(app_gui: "MidiGUI"):
    """
    Hooks the web bridge into the Tk mainloop safely.
    - A command processor runs on the Tk thread via .after(), executing GUI work.
    - A state snapshotter runs periodically so the web UI can read without touching Tk.
    """

    def _seek_to(new_offset: float):
        if app_gui.currently_playing and app_gui.playback_start_time is not None:
            new_offset = float(max(0.0, min(new_offset, app_gui.current_duration or 0.0)))
            app_gui.scrub_slider.set(new_offset)
            # replicate your on_slider_release logic (without mouse events)
            selected = app_gui._enabled_instrument_indices_for_song(app_gui.currently_playing)
            piano_volume_scales = app_gui._piano_volume_scales_for_song(app_gui.currently_playing)
            app_gui._prepare_deferred_audio_start(app_gui.currently_playing, start_offset=new_offset)
            generation = app_gui._prepare_visualizer_for_physical_start(new_offset)
            app_gui.playback_thread.seek(
                app_gui.currently_playing,
                new_offset,
                app_gui._playback_done,
                instrument_indices=selected,
                piano_volume_scales=piano_volume_scales,
                started_callback=app_gui._make_physical_start_callback(app_gui.currently_playing, generation),
                rush_mode=bool(app_gui.rush_mode_enabled.get()),
            )


    def _handle_command(cmd: str, args: dict):
        # Core transport: mutate GUI only on the Tk thread
        if cmd == "pause_toggle":
            app_gui.toggle_pause()
        elif cmd == "stop":
            app_gui.stop_current()
        elif cmd == "set_volume":
            v = int(max(0, min(100, int(args.get("value", 100)))))
            app_gui.volume_slider.set(v)
            app_gui.on_volume_change(v)

        elif cmd == "set_strike_floor":
            pct = int(max(0, min(100, int(args.get("value", 85)))))
            # drive the Tk slider and persist via the existing handler
            try:
                app_gui.strike_slider.set(pct)
            except Exception:
                pass
            app_gui.on_strike_floor_change(pct)
        elif cmd == "set_solenoids":
            app_gui.solenoids_enabled.set(bool(args.get("enabled", True)))
            app_gui.on_solenoids_toggle()
        elif cmd == "set_rush_mode":
            app_gui.rush_mode_enabled.set(bool(args.get("enabled", False))); app_gui.on_rush_mode_toggle()
        elif cmd == "set_loop":
            app_gui.loop_enabled.set(bool(args.get("enabled", False))); app_gui.on_loop_toggle()
        elif cmd == "set_shuffle":
            app_gui.shuffle_enabled.set(bool(args.get("enabled", False))); app_gui.on_shuffle_toggle()
        elif cmd == "set_audio":
            app_gui.audio_enabled.set(bool(args.get("enabled", True))); app_gui.on_audio_toggle()
        elif cmd == "seek":
            _seek_to(float(args.get("seconds", 0)))
        elif cmd == "add_to_queue":
            name = str(args.get("name", "")).strip()
            if not name:
                return

            name_base = os.path.splitext(name)[0].strip()
            name_l = name_base.lower()

            candidate = None
            # 1) Try exact match (case-insensitive) against server-scanned names
            for s in app_gui.all_songs:
                if s.lower() == name_l:
                    for ext in (".mid", ".midi"):
                        p = os.path.join(app_gui.songs_folder, s + ext)
                        if os.path.exists(p):
                            candidate = p
                            break
                if candidate:
                    break

            # 2) Prefix / substring fallback: prefer startswith, only allow substring when
            #    the query is reasonably long to avoid surprising short-match behavior.
            if candidate is None:
                for s in app_gui.all_songs:
                    sl = s.lower()
                    if sl.startswith(name_l) or (len(name_l) >= 4 and name_l in sl):
                        for ext in (".mid", ".midi"):
                            p = os.path.join(app_gui.songs_folder, s + ext)
                            if os.path.exists(p):
                                candidate = p
                                break
                    if candidate:
                        break

            # 3) Last fallback: attempt direct base -> file (previous behavior)
            if candidate is None:
                base = name_base
                for ext in (".mid", ".midi"):
                    p = os.path.join(app_gui.songs_folder, base + ext)
                    if os.path.exists(p):
                        candidate = p
                        break

            if candidate:
                app_gui.queue_files.append(candidate)
                app_gui.refresh_queue()
                if app_gui.currently_playing is None:
                    app_gui.play_next()
            else:
                print(f"[WEB] add_to_queue: no match for '{name}'")

        elif cmd == "remove_queue_index":
            i = int(args.get("index", -1))
            if 0 <= i < len(app_gui.queue_files):
                del app_gui.queue_files[i]
                app_gui.refresh_queue()
        elif cmd == "remove_all":
            app_gui.remove_all()
        elif cmd == "add_all_random":
            app_gui.add_all_random()
        elif cmd == "move_up":
            i = int(args.get("index", -1))
            if 1 <= i < len(app_gui.queue_files):
                app_gui.queue_files[i-1], app_gui.queue_files[i] = app_gui.queue_files[i], app_gui.queue_files[i-1]
                app_gui.refresh_queue()
        elif cmd == "move_down":
            i = int(args.get("index", -1))
            if 0 <= i < len(app_gui.queue_files)-1:
                app_gui.queue_files[i+1], app_gui.queue_files[i] = app_gui.queue_files[i], app_gui.queue_files[i+1]
                app_gui.refresh_queue()
        elif cmd == "scan_songs":
            app_gui.refresh_song_list()
        elif cmd == "set_led":
            # Any subset of these keys is accepted
            changed = False
            for k in ("red","green","blue","brightness","speed"):
                if k in args:
                    _led_cfg[k] = int(max(0, min(100, int(args[k])))) if k!="speed" else int(max(1,min(100,int(args[k]))))
                    changed = True
            if "effect" in args:
                app_gui.led_effect_var.set(str(args["effect"]))
                app_gui.on_effect_change()
                changed = True
            if "idle_effect" in args:
                app_gui.idle_effect_var.set(str(args["idle_effect"]))
                app_gui.on_idle_effect_change()
                changed = True
            if changed:
                _write_led_config(_led_cfg)
                _request_led_render()
        else:
            print(f"[WEB] Unknown command: {cmd}")

    def _process_commands():
        did = 0
        while True:
            try:
                cmd, args = _COMMANDS.get_nowait()
            except queue.Empty:
                break
            did += 1
            try:
                _handle_command(cmd, args or {})
            except Exception as e:
                print(f"[WEB] Command error {cmd}: {e}")
        app_gui.after(50 if did else 150, _process_commands)

    def _snapshot():
        try:
            pos = float(app_gui.scrub_slider.get())
        except Exception:
            pos = 0.0
        try:
            paused = bool(app_gui.playback_thread.is_paused()) if app_gui.currently_playing else False
        except Exception:
            paused = False

        _STATE.update({
            "songs": list(app_gui.all_songs),
            "queue": [os.path.splitext(os.path.basename(p))[0] for p in app_gui.queue_files],
            "currently_playing": (os.path.splitext(os.path.basename(app_gui.currently_playing))[0]
                                  if app_gui.currently_playing else None),
            "paused": paused,
            "volume": int(MASTER_VOLUME),
            "loop": bool(app_gui.loop_enabled.get()),
            "rush_mode": bool(app_gui.rush_mode_enabled.get()),
            "shuffle": bool(app_gui.shuffle_enabled.get()),
            "audio": bool(app_gui.audio_enabled.get()),
            "solenoids": bool(app_gui.solenoids_enabled.get()),
            "pos_seconds": float(pos),
            "duration_seconds": float(app_gui.current_duration or 0.0),
            "strike_floor": int(MIN_STRIKE_FRAC * 100),   # <-- NEW
            "led": dict(_led_cfg),
        })

        app_gui.after(350, _snapshot)

    # Kick off the loops
    app_gui.after(150, _process_commands)
    app_gui.after(200, _snapshot)

class WebServer(threading.Thread):
    def __init__(self, port: int = None, host: str = None):
        super().__init__(daemon=True)
        self.host = host or WEB_HOST
        self.port = int(port or WEB_PORT)
        self.app = Flask(__name__)

        @self.app.get("/api/state")
        def state():
            resp = jsonify(dict(_STATE))        # shallow copy avoids races
            resp.headers["Cache-Control"] = "no-store"   # prevent any caching
            return resp

        @self.app.post("/api/cmd")
        def cmd():
            try:
                data = request.get_json(force=True) or {}
            except Exception:
                data = {}
            action = (data.get("action") or "").strip()
            args = data.get("args") or {}
            if not action:
                return jsonify({"ok": False, "error": "missing action"}), 400
            _enqueue(action, **args)
            return jsonify({"ok": True})

        @self.app.get("/")
        def index():
            return Response(_INDEX_HTML, mimetype="text/html")

    def run(self):
        print(f"[WEB] Serving on http://{self.host}:{self.port}/")
        # Werkzeug dev server is fine for a trusted local LAN control panel.
        self.app.run(host=self.host, port=self.port, threaded=True, use_reloader=False)

_INDEX_HTML = """<!doctype html>
<meta charset="utf-8">
<meta name=viewport content="width=device-width, initial-scale=1">
<title>Pi MIDI Player</title>
<style>
  :root{
    --bg:#1e1e1e; --panel:#232323; --accent:#333333; --fg:#e6e6e6; --sel:#3f3f3f; --muted:#bbbbbb;
    --btn:#2b2b2b; --btn-hover:#3a3a3a; --border:#2a2a2a;
  }
  *{box-sizing:border-box}
  body{font-family:system-ui,-apple-system,Segoe UI,Roboto,Helvetica,Arial,sans-serif;background:var(--bg);color:var(--fg);margin:16px}
  h1{margin:0 0 12px 0}
  section{background:var(--panel);border:1px solid var(--border);border-radius:10px;padding:12px;margin:12px 0}
  .row{display:flex;gap:12px;flex-wrap:wrap;align-items:center}
  .center{align-items:center;justify-content:space-between}
  .grid{display:grid;grid-template-columns:1fr 1fr;gap:12px}
  .mono{font-family:ui-monospace,Menlo,Consolas,monospace}
  label{margin-right:10px}
  button, select, input[type=text]{
    background:var(--btn); color:var(--fg); border:1px solid var(--border); border-radius:8px; padding:6px 10px; font-size:14px
  }
  button:hover{background:var(--btn-hover);cursor:pointer}
  select, input[type=text]{width:100%}
  input[type=range]{width:100%}
  input[type=range]::-webkit-slider-runnable-track{height:6px;background:var(--accent);border-radius:6px}
  input[type=range]::-webkit-slider-thumb{margin-top:-6px; width:18px;height:18px;border-radius:50%;background:#888;border:1px solid #666}
  input[type=range]::-moz-range-track{height:6px;background:var(--accent);border-radius:6px}
  input[type=range]::-moz-range-thumb{width:18px;height:18px;border-radius:50%;background:#888;border:1px solid #666}
  .listbox{height:320px}
  ol#queue{margin:0;padding-left:18px;max-height:320px;overflow:auto}
  ol#queue li{margin:2px 0;padding:2px 4px;background:#1a1a1a;border-radius:6px;display:flex;align-items:center;justify-content:space-between}
  .qtext{flex:1 1 auto;padding-right:8px}
  .qlite{display:flex;gap:6px}
  .tiny{padding:2px 6px;border-radius:6px}
  .pill{background:var(--btn);border:1px solid var(--border);padding:6px 10px;border-radius:10px}
  .muted{color:var(--muted)}
</style>

<h1>Pi MIDI Player</h1>

<section>
  <div class="row center">
    <div class="row">
      <button id=toggle>Pause/Resume</button>
      <button id=stop>Stop Current</button>
    </div>
    <div>Currently Playing: <b id=now class=mono>(none)</b></div>
  </div>

<div class="row" style="margin-top:8px">
  <div style="flex:1 1 520px">
    <label>Position <span id=posTxt class=mono>0.0 / 0.0 s</span></label>
    <input id=seek type=range min=0 max=0 step=0.1 value=0>
  </div>
  <div style="flex:0 0 260px">
    <label>Volume <span id=volTxt class=mono>100%</span></label>
    <input id=vol type=range min=0 max=100 step=1>
  </div>
</div>

<!-- Strike Floor row -->
<div class="row" style="margin-top:4px">
  <div style="flex:0 0 260px">
    <label>Strike Floor <span id=strikeTxt class=mono>85%</span></label>
    <input id=strike type=range min=0 max=100 step=1>
  </div>
</div>


  <div class="row" style="margin-top:4px">
    <label class=pill><input type=checkbox id=solenoids> Solenoids</label>
    <label class=pill><input type=checkbox id=rushMode> Rush Mode</label>
    <label class=pill><input type=checkbox id=loop> Loop</label>
    <label class=pill><input type=checkbox id=shuffle> Shuffle</label>
    <label class=pill><input type=checkbox id=audio> Audio</label>
  </div>
</section>

<section>
  <div class="grid">
    <!-- LEFT: Songs -->
    <div>
      <div class="row" style="justify-content:space-between;align-items:flex-end">
        <div><h3 style="margin:0">Songs</h3><div class="muted" style="font-size:12px">Search filters locally</div></div>
        <div class="row">
          <button id="add" class="tiny">âž• Add to Queue</button>
          <button id="addall" class="tiny">ðŸŽ² Add All (Random)</button>
        </div>
      </div>
      <div style="margin-top:6px">
        <input id="search" type="text" placeholder="Search ðŸ”" />
      </div>
      <div style="margin-top:6px">
        <select id=songs size=16 class=listbox></select>
      </div>
    </div>

    <!-- RIGHT: Queue -->
    <div>
      <div class="row" style="justify-content:space-between;align-items:center">
        <h3 style="margin:0">Playback Queue</h3>
        <button id=rmAll class=tiny>Remove All</button>
      </div>
      <ol id=queue style="margin-top:6px"></ol>
    </div>
  </div>
</section>

<section>
  <h3 style="margin-top:0">LED Light Controls</h3>
  <div class="grid">
    <!-- LEFT column -->
    <div>
      <div>
        <label>Brightness <span id=brTxt class=mono></span></label>
        <input id=br type=range min=0 max=100 step=1>
      </div>
      <div class="row" style="margin-top:6px">
        <div style="flex:1">
          <label>Effect</label>
          <select id=eff>
            <option>Solid</option><option>RGB</option><option>Random RGB</option>
            <option>Rainbow Effect</option><option>Moving Rainbow</option>
            <option>Dancing</option><option>Flicker</option><option>Christmas</option><option>Track</option>
          </select>
        </div>
        <div style="flex:1">
          <label>Idle Effect</label>
          <select id=idle>
            <option>Off</option><option>Solid</option><option>L->R Rainbow</option>
            <option>R->L Rainbow</option><option>Rainbow</option><option>RGB Cable</option>
            <option>RGB Cable Gaps</option><option>4th of July</option><option>Flicker</option><option>Christmas</option>
          </select>
        </div>
      </div>
      <div style="margin-top:6px">
        <label>Idle Speed <span id=idleTxt class=mono></span></label>
        <input id=idleSpeed type=range min=1 max=100 step=1>
      </div>
    </div>

    <!-- RIGHT column -->
    <div>
      <div>
        <label>Red <span id=redTxt class=mono></span></label>
        <input id=red type=range min=0 max=100 step=1>
      </div>
      <div style="margin-top:6px">
        <label>Green <span id=greenTxt class=mono></span></label>
        <input id=green type=range min=0 max=100 step=1>
      </div>
      <div style="margin-top:6px">
        <label>Blue <span id=blueTxt class=mono></span></label>
        <input id=blue type=range min=0 max=100 step=1>
      </div>
    </div>
  </div>
</section>

<script>
const $ = (id)=>document.getElementById(id);
async function post(action, args={}) {
  await fetch('/api/cmd', {method:'POST', headers:{'Content-Type':'application/json'},
    body: JSON.stringify({action, args})});
}

/* --- Controls --- */
$("toggle").onclick = ()=>post('pause_toggle');
$("stop").onclick   = ()=>post('stop');

/* --- Songs actions --- */
/* Desktop: double-click to add */
$("songs").addEventListener("dblclick", () => {
  const opt = $("songs").selectedOptions[0];
  if (opt) post("add_to_queue", { name: opt.value });
});
/* Button: add selected */
$("add").onclick = ()=>{
  const opt = $("songs").selectedOptions[0];
  if (opt) post("add_to_queue", { name: opt.value });
};
/* Mobile: change selection -> add */
$("songs").addEventListener("change", () => {
  if (/Mobi|Android|iPhone|iPad|Mobile/i.test(navigator.userAgent)) {
    const opt = $("songs").selectedOptions[0];
    if (opt) post("add_to_queue", { name: opt.value });
  }
});
/* Add all (random order) */
$("addall").onclick = ()=>post('add_all_random');

/* --- Queue actions --- */
$("rmAll").onclick  = ()=>post('remove_all');

/* --- Sliders --- */
$("vol").oninput = (e)=>{ $("volTxt").textContent = e.target.value+"%"; post('set_volume', {value: Number(e.target.value)}); };
$("seek").onchange = (e)=>post('seek', {seconds: Number(e.target.value)});
$("strike").oninput = (e)=>{ $("strikeTxt").textContent = e.target.value+"%"; post('set_strike_floor', {value: Number(e.target.value)}); };  // NEW


/* --- Toggles --- */
$("solenoids").onchange = (e)=>post('set_solenoids', {enabled: e.target.checked});
$("rushMode").onchange  = (e)=>post('set_rush_mode', {enabled: e.target.checked});
$("loop").onchange      = (e)=>post('set_loop',      {enabled: e.target.checked});
$("shuffle").onchange   = (e)=>post('set_shuffle',   {enabled: e.target.checked});
$("audio").onchange     = (e)=>post('set_audio',     {enabled: e.target.checked});

/* --- LED controls --- */
$("br").oninput      = (e)=>{ $("brTxt").textContent=e.target.value+"%"; post('set_led', {brightness:Number(e.target.value)})};
$("eff").onchange    = (e)=>post('set_led', {effect:e.target.value});
$("idle").onchange   = (e)=>post('set_led', {idle_effect:e.target.value});
$("idleSpeed").oninput=(e)=>{ $("idleTxt").textContent=e.target.value; post('set_led', {speed:Number(e.target.value)})};

$("red").oninput   = (e)=>{ $("redTxt").textContent=e.target.value;   post('set_led', {red:Number(e.target.value)})};
$("green").oninput = (e)=>{ $("greenTxt").textContent=e.target.value; post('set_led', {green:Number(e.target.value)})};
$("blue").oninput  = (e)=>{ $("blueTxt").textContent=e.target.value;  post('set_led', {blue:Number(e.target.value)})};

/* --- Queue item rendering --- */
function renderQueue(arr){
  const q = $("queue"); q.innerHTML="";
  arr.forEach((name, i)=>{
    const li = document.createElement('li');
    const text = document.createElement('span'); text.className="qtext"; text.textContent = name;
    const up = document.createElement('button'); up.textContent="â†‘"; up.className="tiny"; up.onclick=()=>post('move_up',{index:i});
    const dn = document.createElement('button'); dn.textContent="â†“"; dn.className="tiny"; dn.onclick=()=>post('move_down',{index:i});
    const rm = document.createElement('button'); rm.textContent="âœ–"; rm.className="tiny"; rm.onclick=()=>post('remove_queue_index',{index:i});
    const btns = document.createElement('span'); btns.className="qlite"; btns.appendChild(up); btns.appendChild(dn); btns.appendChild(rm);
    li.appendChild(text); li.appendChild(btns); q.appendChild(li);
  });
}

/* --- Search filter (client-side) --- */
let ALL_SONGS = [];
$("search").addEventListener('input', ()=>applyFilter());
function applyFilter(){
  const term = $("search").value.trim().toLowerCase();
  const sel = $("songs");
  const list = term ? ALL_SONGS.filter(s => s.toLowerCase().includes(term)) : ALL_SONGS.slice();
  const cur = sel.value;

  // Build options safely using DOM methods (avoid innerHTML)
  sel.innerHTML = "";
  list.forEach(n => {
    const opt = document.createElement("option");
    opt.value = n;
    opt.textContent = n; // safe text (no HTML parsing)
    sel.appendChild(opt);
  });

  if (cur && list.includes(cur)) sel.value = cur;
}


/* --- State refresh --- */
async function refresh(){
  try{
    const s = await fetch('/api/state').then(r=>r.json());

    $("now").textContent = s.currently_playing ? (s.paused?"[Paused] ":"")+s.currently_playing : "(none)";
    $("vol").value = s.volume; $("volTxt").textContent = s.volume+"%";
    // NEW: strike floor
    if (typeof s.strike_floor !== "undefined") {
      $("strike").value = s.strike_floor;
      $("strikeTxt").textContent = s.strike_floor + "%";
    }
    $("solenoids").checked = !!s.solenoids;
    $("loop").checked = !!s.loop;
    $("rushMode").checked = !!s.rush_mode;
    $("shuffle").checked = !!s.shuffle;
    $("audio").checked = !!s.audio;

    $("seek").max   = s.duration_seconds||0;
    $("seek").value = s.pos_seconds||0;
    $("posTxt").textContent = (s.pos_seconds||0).toFixed(1)+" / "+(s.duration_seconds||0).toFixed(1)+" s";

    // songs (auto-updating via watchdog -> state polling)
    const songs = s.songs || [];
    if (JSON.stringify(ALL_SONGS) !== JSON.stringify(songs)){
      ALL_SONGS = songs;
      applyFilter();
    }

    // ensure one option is selected so the collapsed mobile <select> shows a value
    const sel = $("songs");
    if (!sel.value && ALL_SONGS.length) sel.value = ALL_SONGS[0];

    renderQueue(s.queue||[]);

    // LED current values
    const led = s.led || {};
    $("br").value = (typeof led.brightness !== "undefined") ? led.brightness : 100;
    $("brTxt").textContent = $("br").value + "%";
    if (led.effect) $("eff").value = led.effect;
    if (led.idle_effect) $("idle").value = led.idle_effect;
    $("idleSpeed").value = (typeof led.speed !== "undefined") ? led.speed : 20;
    $("idleTxt").textContent = $("idleSpeed").value;

    $("red").value   = (typeof led.red   !== "undefined") ? led.red   : 100; $("redTxt").textContent   = $("red").value;
    $("green").value = (typeof led.green !== "undefined") ? led.green : 100; $("greenTxt").textContent = $("green").value;
    $("blue").value  = (typeof led.blue  !== "undefined") ? led.blue  : 100; $("blueTxt").textContent  = $("blue").value;
  }catch(e){ /* ignore transient errors */ }
}
refresh(); setInterval(refresh, 800);
</script>
"""




if __name__ == "__main__":
    main()
