from z3 import *

# Convert blocked times to minutes since 9:00 for Monday
participants = {
    "Joan": [(150, 180), (330, 360)],
    "Megan": [(0, 60), (300, 330), (420, 450)],
    "Austin": [],
    "Betty": [(30, 60), (150, 180), (210, 240), (420, 450)],
    "Judith": [(0, 120), (180, 240), (300, 360)],
    "Terry": [(30, 60), (150, 210), (240, 300), (360, 390), (420, 480)],
    "Kathryn": [(30, 60), (90, 120), (150, 240), (300, 420), (450, 480)]
}

# Create solver and variables
s = Optimize()
start = Int('start')

# Basic constraints: 30min meeting within work hours (0-480 minutes)
s.add(start >= 0)
s.add(start + 30 <= 480)

# Add constraints for each participant's busy periods
for name, blocks in participants.items():
    for (busy_start, busy_end) in blocks:
        s.add(Or(start + 30 <= busy_start, start >= busy_end))

# Find earliest possible time
s.minimize(start)

if s.check() == sat:
    m = s.model()
    start_val = m[start].as_long()
    # Convert to HH:MM format
    start_h = 9 + start_val // 60
    start_m = start_val % 60
    end_val = start_val + 30
    end_h = 9 + end_val // 60
    end_m = end_val % 60
    print(f"Day: Monday, Start: {start_h:02}:{start_m:02}, End: {end_h:02}:{end_m:02}")
else:
    print("No solution found")