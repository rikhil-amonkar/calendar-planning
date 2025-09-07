from z3 import *

# Create a Z3 solver
solver = Solver()

# Define constants
duration = 30  # meeting duration in minutes
work_start = 0            # 9:00 is represented as 0 minutes offset from 9:00
work_end = 480            # 17:00 is 480 minutes after 9:00

# Define variables:
# day: 0 for Monday, 1 for Tuesday.
# start: meeting start time in minutes offset from 9:00.
day = Int('day')
start = Int('start')

# Meeting must be within working hours:
solver.add(start >= work_start, start + duration <= work_end)

# Day must be either Monday (0) or Tuesday (1)
solver.add(Or(day == 0, day == 1))

# Constraint: Nathan cannot meet on Monday
solver.add(day == 1)

# Constraint: Amanda does not want to meet on Tuesday after 11:00.
# 11:00 is 120 minutes after 9:00, so meeting must end by 11:00.
solver.add(Implies(day == 1, start + duration <= 120))

# Define busy intervals for each participant, in minutes relative to 9:00.
# For example, an interval of [9:00,10:30] becomes [0, 90].
busy_intervals = {
    "Amanda": {
        # Monday busy intervals
        0: [(0, 90), (120, 150), (210, 240), (270, 300), (330, 360)],
        # Tuesday busy intervals
        1: [(0, 30), (60, 90), (150, 180), (270, 330), (390, 420), (450, 480)]
    },
    "Nathan": {
        # Monday busy intervals
        0: [(60, 90), (120, 150), (270, 330), (420, 450)],
        # Tuesday busy intervals
        1: [(0, 90), (120, 240), (270, 300), (330, 390), (420, 450)]
    }
}

# For each busy interval, add the constraint that the meeting must not overlap with it.
# Two time intervals [a, b) and [c, d) do not overlap if either b <= c or a >= d.
for person in busy_intervals:
    for d in busy_intervals[person]:
        for (busy_start, busy_end) in busy_intervals[person][d]:
            # If the meeting is on day 'd', then it must either finish before the busy interval starts
            # or start after the busy interval ends.
            solver.add(Implies(day == d, Or(start + duration <= busy_start, start >= busy_end)))

# Solve the constraints
if solver.check() == sat:
    model = solver.model()
    chosen_day = model[day].as_long()
    chosen_start = model[start].as_long()  # minutes offset from 9:00
    
    # Convert minutes to HH:MM (we use 9:00 as base time)
    start_hour = 9 + chosen_start // 60
    start_min = chosen_start % 60
    end_time = chosen_start + duration
    end_hour = 9 + end_time // 60
    end_min = end_time % 60
    
    # Get the day string
    day_str = "Monday" if chosen_day == 0 else "Tuesday"
    
    # Format the output as "Day HH:MM:HH:MM"
    meeting_time = f"{start_hour:02d}:{start_min:02d}:{end_hour:02d}:{end_min:02d}"
    print(f"{day_str} {meeting_time}")
else:
    print("No solution found.")