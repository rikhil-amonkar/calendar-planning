from z3 import *

# Define busy intervals for each participant and day
eugene_busy = {
    0: [(120, 180), (270, 300), (330, 360), (420, 450)],  # Monday
    2: [(0, 30), (120, 150), (180, 210), (270, 360)],    # Wednesday
    3: [(30, 60), (120, 210)],                           # Thursday
    4: [(90, 120), (180, 210), (240, 270)],              # Friday
}

eric_busy = {
    0: [(0, 480)],  # Monday
    1: [(0, 480)],  # Tuesday
    2: [(0, 150), (180, 300), (330, 450)],  # Wednesday
    3: [(0, 480)],  # Thursday
    4: [(0, 120), (150, 480)],  # Friday
}

# Create solver
s = Solver()

# Variables
day = Int('day')
start = Int('start')

# Constraints on day and start
s.add(0 <= day, day <= 4)
s.add(0 <= start, start <= 450)
s.add(day != 2)  # Avoid Wednesday

# For each day, add constraints for busy intervals
for d in range(5):
    # Eugene's busy intervals on day d
    for (b_start, b_end) in eugene_busy.get(d, []):
        s.add(Implies(day == d, Or(start + 30 <= b_start, start >= b_end)))
    # Eric's busy intervals on day d
    for (b_start, b_end) in eric_busy.get(d, []):
        s.add(Implies(day == d, Or(start + 30 <= b_start, start >= b_end)))

# Check if solution exists
if s.check() == sat:
    m = s.model()
    day_val = m[day].as_long()
    start_val = m[start].as_long()
    # Convert to day name
    days = ["Monday", "Tuesday", "Wednesday", "Thursday", "Friday"]
    day_name = days[day_val]
    # Convert start_val to hours and minutes
    start_h = 9 + start_val // 60
    start_m = start_val % 60
    end_val = start_val + 30
    end_h = 9 + end_val // 60
    end_m = end_val % 60
    # Format time as HH:MM:HH:MM
    time_str = f"{start_h:02d}:{start_m:02d}:{end_h:02d}:{end_m:02d}"
    print(f"{day_name} {time_str}")
else:
    print("No solution found")