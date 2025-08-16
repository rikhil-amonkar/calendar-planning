from z3 import *

# We'll represent time as minutes from midnight.
# Work hours: 09:00 is 540 and 17:00 is 1020. Meeting duration is 30 minutes.
# The meeting start time must be in [540, 1020-30] => [540, 990].
meeting_start = Int('meeting_start')
meeting_duration = 30

# Define the busy intervals (start, end) for each participant in minutes.
# Eric is free all day so no busy intervals.
# Ashley's busy intervals:
ashley_busy = [
    (600, 630),   # 10:00 to 10:30
    (660, 720),   # 11:00 to 12:00
    (750, 780),   # 12:30 to 13:00
    (900, 960)    # 15:00 to 16:00
]
# Ronald's busy intervals:
ronald_busy = [
    (540, 570),   # 9:00 to 9:30
    (600, 690),   # 10:00 to 11:30
    (750, 840),   # 12:30 to 14:00
    (870, 1020)   # 14:30 to 17:00
]
# Larry's busy intervals:
larry_busy = [
    (540, 720),   # 9:00 to 12:00
    (780, 1020)   # 13:00 to 17:00
]

# Combine all busy intervals into one list.
busy_intervals = ashley_busy + ronald_busy + larry_busy

# Create a Z3 solver.
solver = Solver()

# Constraint: meeting must start within work hours.
solver.add(meeting_start >= 540, meeting_start <= 990)

# For every busy interval [a, b] the meeting interval [meeting_start, meeting_start+30]
# must not overlap. Two intervals [s, s+duration] and [a, b] don't overlap if either:
# the meeting ends at or before a (i.e., meeting_start+30 <= a) or starts at or after b (i.e., meeting_start >= b).
for (a, b) in busy_intervals:
    solver.add(Or(meeting_start + meeting_duration <= a, meeting_start >= b))

# Solve the constraints.
if solver.check() == sat:
    model = solver.model()
    start_val = model[meeting_start].as_long()
    end_val = start_val + meeting_duration
    
    # Convert minutes to HH:MM (24-hour format)
    start_hour, start_minute = divmod(start_val, 60)
    end_hour, end_minute = divmod(end_val, 60)
    
    # Format the solution output as required.
    solution_text = (
        "SOLUTION:\n"
        "Day: Monday\n"
        "Start Time: {:02}:{:02}\n"
        "End Time: {:02}:{:02}".format(start_hour, start_minute, end_hour, end_minute)
    )
    print(solution_text)
else:
    print("No solution found.")