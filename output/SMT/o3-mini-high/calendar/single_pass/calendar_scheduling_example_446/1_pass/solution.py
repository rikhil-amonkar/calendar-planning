from z3 import Solver, Int, Or, sat

# Duration of the meeting in minutes
duration = 30

# Define meeting start time (in minutes after midnight)
s = Int('s')

solver = Solver()

# Working hours: 9:00 to 17:00 (i.e., 540 minutes to 1020 minutes)
solver.add(s >= 540)
solver.add(s + duration <= 1020)

# Busy intervals are expressed as (start, end) in minutes after midnight.
# (For example, 9:00 is 540, 9:30 is 570, etc.)
busy_intervals = [
    # Megan's busy times
    (540, 570),   # 9:00 to 9:30
    (600, 660),   # 10:00 to 11:00
    (720, 750),   # 12:00 to 12:30

    # Christine's busy times
    (540, 570),   # 9:00 to 9:30
    (690, 720),   # 11:30 to 12:00
    (780, 840),   # 13:00 to 14:00
    (930, 990),   # 15:30 to 16:30

    # Gabriel is free all day (no busy intervals)

    # Sara's busy times
    (690, 720),   # 11:30 to 12:00
    (870, 900),   # 14:30 to 15:00

    # Bruce's busy times
    (570, 600),   # 9:30 to 10:00
    (630, 720),   # 10:30 to 12:00
    (750, 840),   # 12:30 to 14:00
    (870, 900),   # 14:30 to 15:00
    (930, 990),   # 15:30 to 16:30

    # Kathryn's busy times
    (600, 930),   # 10:00 to 15:30
    (960, 990),   # 16:00 to 16:30

    # Billy's busy times
    (540, 570),   # 9:00 to 9:30
    (660, 690),   # 11:00 to 11:30
    (720, 840),   # 12:00 to 14:00
    (870, 930)    # 14:30 to 15:30
]

# For each busy interval, ensure the meeting does not overlap.
# That is, the meeting [s, s+duration] must either finish by busy_start or start after busy_end.
for (busy_start, busy_end) in busy_intervals:
    solver.add(Or(s + duration <= busy_start, s >= busy_end))

# Find a meeting time that works for all participants.
if solver.check() == sat:
    m = solver.model()
    start_min = m[s].as_long()
    end_min = start_min + duration

    # Convert minutes after midnight to HH:MM in 24-hour format.
    start_hour = start_min // 60
    start_minute = start_min % 60
    end_hour = end_min // 60
    end_minute = end_min % 60

    start_str = f"{start_hour:02d}:{start_minute:02d}"
    end_str = f"{end_hour:02d}:{end_minute:02d}"

    # Output the solution in the required format.
    print("SOLUTION:")
    print("Day: Monday")
    print("Start Time: " + start_str)
    print("End Time: " + end_str)
else:
    print("No solution found.")