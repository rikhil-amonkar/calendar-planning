# Tmux Quick Reference

## Basic Commands

```bash
# Start new session
tmux

# Start new named session
tmux new -s session_name

# List sessions
tmux ls

# Attach to session
tmux attach -t session_name
tmux a -t session_name

# Detach from session
Ctrl+b d

# Kill session
tmux kill-session -t session_name
```

## Key Bindings (Prefix: `Ctrl+b`)

### Session Management
```
Ctrl+b d          Detach from session
Ctrl+b s          List sessions (interactive)
Ctrl+b $          Rename session
```

### Window Management
```
Ctrl+b c          Create new window
Ctrl+b ,          Rename window
Ctrl+b w          List windows
Ctrl+b n          Next window
Ctrl+b p          Previous window
Ctrl+b 0-9        Switch to window number
Ctrl+b &          Kill window
```

### Pane Management
```
Ctrl+b %          Split vertically (creates right pane)
Ctrl+b "          Split horizontally (creates bottom pane)
Ctrl+b ←→↑↓       Navigate panes
Ctrl+b o          Switch to next pane
Ctrl+b ;          Switch to previous pane
Ctrl+b x          Kill pane
Ctrl+b z          Zoom/unzoom pane (toggle)
Ctrl+b q          Show pane numbers
Ctrl+b {          Swap pane with previous
Ctrl+b }          Swap pane with next
Ctrl+b h          Resize pane left
Ctrl+b j          Resize pane down
Ctrl+b k          Resize pane up
Ctrl+b l          Resize pane right
Ctrl+b Space      Toggle between layouts
```

### Copy Mode
```
Ctrl+b [          Enter copy mode
q                 Exit copy mode
Space             Start selection
Enter             Copy selection
Ctrl+b ]          Paste
```

### Other Useful Commands
```
Ctrl+b ?          List all key bindings
Ctrl+b t          Show clock
Ctrl+b :          Enter command mode
Ctrl+b r          Reload config file
```

## Command Mode (`Ctrl+b :`)

```bash
# Switch to window
:swap-window -s 2 -t 1    # Swap window 2 with window 1
:kill-window -t 3         # Kill window 3
:rename-window NAME       # Rename current window
:new-window -n NAME       # Create new named window

# Pane commands
:split-window              # Split window horizontally
:split-window -h           # Split window vertically
:kill-pane                 # Kill current pane
```

## Common Workflows

```bash
# Quick session start with name
tmux new -s work

# Start session in detached mode
tmux new -d -s background

# Attach to last session
tmux attach

# Send command to all panes
Ctrl+b : setw synchronize-panes

# Save tmux environment
Ctrl+b : set-option -g @resurrect-strategy-vim 'session'

# Reload config
Ctrl+b : source-file ~/.tmux.conf
```

## Configuration Tips

### Basic ~/.tmux.conf
```
# Set prefix to Ctrl+a (easier than Ctrl+b)
unbind C-b
set-option -g prefix C-a
bind-key C-a send-prefix

# Enable mouse support
set -g mouse on

# Start windows and panes at 1, not 0
set -g base-index 1
setw -g pane-base-index 1

# Reload config easily
bind r source-file ~/.tmux.conf \; display "Config reloaded!"
```

## Quick Tips

- `tmux a` - Attach to most recent session
- `tmux kill-server` - Kill all sessions
- `Ctrl+b d` - Detach (session keeps running)
- `Ctrl+b z` - Zoom pane to full screen (press again to unzoom)
- `Ctrl+b :` - Command prompt for advanced operations
