# PianoPi

PianoPi is a Raspberry Pi 5 MIDI player for a solenoid-driven piano/keyboard rig.
It plays MIDI files through physical solenoids, mirrors notes to an LED strip, can play speaker audio through FluidSynth, and includes a Tkinter control UI plus a local web control page.

## Features

- Tkinter touchscreen-friendly MIDI player
- Physical solenoid playback through PCA9685 boards
- Sustain pedal control through MIDI CC64
- LED strip note mirroring and idle effects
- FluidSynth speaker playback
- Instrument/track mixer
- Keyboard recording support when `real_piano` is false
- Local web control page on port 8000 by default
- CSV play history log

## Hardware this was built for

- Raspberry Pi 5, 64-bit Raspberry Pi OS
- PCA9685 PWM boards for solenoids
- `pi5neo` LED strip control
- FluidSynth with a General MIDI soundfont
- Optional USB MIDI keyboard for keyboard test mode

## Install system packages

```
sudo apt update
sudo apt install -y python3-pip python3-tk fluidsynth fluid-soundfont-gm alsa-utils git
```

For the local web UI and visualizer, you may also want Chromium installed:

```
sudo apt install -y chromium-browser
```

## Install Python dependencies

```
python3 -m pip install -r requirements.txt
```

On the Pi with hardware attached:

```
python3 -m pip install -r requirements-pi.txt
```

## Configure

Copy the example config:

```
cp player_config.example.json player_config.json
```

Edit `player_config.json`:

```json
{
  "midi_dir": "/home/pi5/Desktop/midiMusicFiles",
  "sound_font": "/usr/share/sounds/sf2/FluidR3_GM.sf2",
  "real_piano": false,
  "touchscreen_osk_auto_show": true,
  "web_host": "0.0.0.0",
  "web_port": 8000
}
```

`real_piano` controls which hardware mode/profile is used:

- `false`: keyboard test rig mode, with recording buttons visible
- `true`: real acoustic piano mode

You can also override a few settings with environment variables:

```
PIANOPI_MIDI_DIR=/path/to/midi PIANOPI_WEB_HOST=127.0.0.1 python3 PianoPi.py
```

## Run

```
python3 PianoPi.py
```

## Web control page

By default the web server binds to:

```text
0.0.0.0:8000
```

That means it listens on all network interfaces so another device on the same trusted local network can open:

http://<your-pi-ip>:8000/
```
