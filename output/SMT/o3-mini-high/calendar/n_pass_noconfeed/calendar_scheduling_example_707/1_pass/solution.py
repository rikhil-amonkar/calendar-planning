from z3 import *

# Meeting duration (in minutes)
duration = 30

# We'll represent time as minutes offset from 9:00.
# s is the start time (in minutes from 9:00), and it must be between 0 (9:00) and 450 (16:30 start so that meeting ends by 17:00).
s = Int('s')
# d represents the day: 0 = Monday, 1 = Tuesday, 2 = Wednesday.
# But Ryan cannot meet on Wednesday, so effectively d ∈ {0, 1}.
d = Int('d')

solver = Solver()
# Working hour constraint: meeting must lie within [9:00,17:00]
solver.add(s >= 0, s <= 450)

# d must be either 0 (Monday) or 1 (Tuesday) [since Ryan cannot meet on Wednesday]
solver.add(Or(d == 0, d == 1))

# Adam would like to avoid Monday meetings before 14:30.
# 14:30 is 5.5 hours after 9:00, i.e. 330 minutes.
solver.add(Implies(d == 0, s >= 330))

# Define busy intervals in minutes relative to 9:00.
# For each interval, the non-overlap condition for a meeting starting at s with duration
# is: s + duration <= busy_start or s >= busy_end.
# Ryan's busy intervals
monday_ryan = [(30, 60), (120, 180), (240, 270), (390, 420)]
tuesday_ryan = [(150, 210), (390, 420)]
# Adam's busy intervals
monday_adam = [(0, 90), (120, 270), (300, 420), (450, 480)]
tuesday_adam = [(0, 60), (90, 390), (420, 480)]

# Add Monday constraints (d == 0)
for busy_start, busy_end in monday_ryan:
    solver.add(Implies(d == 0, Or(s + duration <= busy_start, s >= busy_end)))
for busy_start, busy_end in monday_adam:
    solver.add(Implies(d == 0, Or(s + duration <= busy_start, s >= busy_end)))

# Add Tuesday constraints (d == 1)
for busy_start, busy_end in tuesday_ryan:
    solver.add(Implies(d == 1, Or(s + duration <= busy_start, s >= busy_end)))
for busy_start, busy_end in tuesday_adam:
    solver.add(Implies(d == 1, Or(s + duration <= busy_start, s >= busy_end)))

if solver.check() == sat:
    model = solver.model()
    meeting_day = model[d].as_long()  # 0: Monday, 1: Tuesday
    meeting_start = model[s].as_long()  # Minutes offset from 9:00

    # Compute actual start and end times:
    start_total = 9 * 60 + meeting_start  # in minutes from midnight
    end_total = start_total + duration

    start_hour = start_total // 60
    start_minute = start_total % 60
    end_hour = end_total // 60
    end_minute = end_total % 60

    # Map day number to day name
    day_map = {0: "Monday", 1: "Tuesday"}
    day_name = day_map.get(meeting_day, "Unknown")

    # Format time range as HH:MM:HH:MM (start and end)
    time_range = f"{start_hour:02d}:{start_minute:02d}:{end_hour:02d}:{end_minute:02d}"
    print(day_name, time_range)
else:
    print("No solution found.")