from z3 import *

# Convert blocked times to minutes since 9:00 for Monday
participants = {
    "Diane": [(30, 60), (330, 360)],
    "Jack": [(270, 300), (330, 360)],
    "Eugene": [(0, 60), (90, 150), (180, 330), (360, 450)],
    "Patricia": [(30, 90), (120, 180), (210, 300), (360, 450)]
}

# Create solver and variables
s = Optimize()
start = Int('start')

# Basic constraints: 30min meeting within work hours
s.add(start >= 0)
s.add(start + 30 <= 480)  # 17:00 = 480 minutes

# Add constraints for each participant's busy periods
for name, blocks in participants.items():
    for (busy_start, busy_end) in blocks:
        # Meeting must either end before busy period or start after
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