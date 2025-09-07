from z3 import *

# Meeting duration in minutes
meeting_duration = 30

# Create Z3 solver instance
solver = Solver()

# s: meeting start time in minutes after 9:00 (so 0 = 9:00, 480 = 17:00)
s = Int('s')
# d: day index: 0 for Monday, 1 for Tuesday, 2 for Wednesday
d = Int('d')

# Working hours constraint: meeting must fit between 9:00 and 17:00
solver.add(s >= 0, s + meeting_duration <= 480)
# Day must be one of 0, 1, or 2
solver.add(Or(d == 0, d == 1, d == 2))

# Define Jennifer's busy intervals for each day (in minutes after 9:00)
busy_intervals = {
    0: [  # Monday: Jennifer's meetings: 9:00-11:00, 11:30-13:00, 13:30-14:30, 15:00-17:00
        (0, 120),
        (150, 240),
        (270, 330),
        (360, 480)
    ],
    1: [  # Tuesday: 9:00-11:30, 12:00-17:00
        (0, 150),
        (180, 480)
    ],
    2: [  # Wednesday: 9:00-11:30, 12:00-12:30, 13:00-14:00, 14:30-16:00, 16:30-17:00
        (0, 150),
        (180, 210),
        (240, 300),
        (330, 420),
        (450, 480)
    ]
}

# For each day, add constraints that the meeting time must not clash 
# with any of Jennifer's busy intervals.
for day in busy_intervals:
    for (busy_start, busy_end) in busy_intervals[day]:
        # If the meeting is on 'day', then it must either finish by the start of the busy interval
        # or start after the busy interval ends.
        solver.add(Implies(d == day, Or(s + meeting_duration <= busy_start, s >= busy_end)))

# John's preference: He would like to avoid meetings on Monday after 14:30.
# 14:30 corresponds to 5.5 hours after 9:00 which is 330 minutes.
# To finish by 14:30, we require s + meeting_duration <= 330 when day is Monday.
solver.add(Implies(d == 0, s + meeting_duration <= 330))

# Check if the constraints are satisfiable and output a solution
if solver.check() == sat:
    model = solver.model()
    meeting_day = model[d].as_long()
    meeting_start = model[s].as_long()

    # Convert the meeting start time (minutes after 9:00) to HH:MM format.
    start_hour = 9 + meeting_start // 60
    start_minute = meeting_start % 60
    end_time = meeting_start + meeting_duration
    end_hour = 9 + end_time // 60
    end_minute = end_time % 60

    # Map day indices to day names
    day_names = {0: "Monday", 1: "Tuesday", 2: "Wednesday"}
    day_str = day_names.get(meeting_day, "Unknown")

    # Format the time range as HH:MM:HH:MM
    time_range = f"{start_hour:02d}:{start_minute:02d}:{end_hour:02d}:{end_minute:02d}"
    print(f"Day: {day_str}")
    print(f"Time Range: {{{time_range}}}")
else:
    print("No valid meeting time found.")