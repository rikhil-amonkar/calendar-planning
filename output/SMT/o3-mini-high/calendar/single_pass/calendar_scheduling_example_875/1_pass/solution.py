from z3 import *

# Map days to numbers: 0=Monday, 1=Tuesday, 2=Wednesday, 3=Thursday.
day_names = {0: "Monday", 1: "Tuesday", 2: "Wednesday", 3: "Thursday"}

# Create solver
s = Solver()

# Variables:
# 'day' is an integer variable representing the day.
# 'start' is the meeting start time in minutes from midnight.
day = Int('day')
start = Int('start')
duration = 60  # meeting duration in minutes

# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes).
s.add(day >= 0, day <= 3)
s.add(start >= 540, start + duration <= 1020)

# Busy intervals are given in minutes from midnight.
# Natalie’s busy times
natalie_busy = {
    0: [(540, 570), (600, 720), (750, 780), (840, 870), (900, 990)],  # Monday
    1: [(540, 570), (600, 630), (750, 840), (960, 1020)],               # Tuesday
    2: [(660, 690), (960, 990)],                                         # Wednesday
    3: [(600, 660), (690, 900), (930, 960), (990, 1020)]                  # Thursday
}

# William’s busy times
william_busy = {
    0: [(570, 660), (690, 1020)],        # Monday
    1: [(540, 780), (810, 960)],         # Tuesday
    2: [(540, 750), (780, 870), (930, 960), (990, 1020)],  # Wednesday
    3: [(540, 630), (660, 690), (720, 750), (780, 840), (900, 1020)]  # Thursday
}

# For each day and each busy interval, if the meeting is on that day then
# the meeting interval [start, start+60] must not intersect the busy interval.
# In other words, for each busy interval [b_start,b_end]:
#   either the meeting ends before the busy interval starts: start + 60 <= b_start
#   or it starts after the busy interval ends: start >= b_end.
for d in range(4):
    for (b_start, b_end) in natalie_busy[d]:
        s.add(Implies(day == d, Or(start + duration <= b_start, start >= b_end)))
    for (b_start, b_end) in william_busy[d]:
        s.add(Implies(day == d, Or(start + duration <= b_start, start >= b_end)))

# Check for a solution.
if s.check() == sat:
    m = s.model()
    meeting_day = m[day].as_long()
    meeting_start = m[start].as_long()
    meeting_end = meeting_start + duration

    # Convert minutes back to HH:MM format.
    def format_time(t):
        hours = t // 60
        minutes = t % 60
        return f"{hours:02d}:{minutes:02d}"

    print("SOLUTION:")
    print("Day: " + day_names[meeting_day])
    print("Start Time: " + format_time(meeting_start))
    print("End Time: " + format_time(meeting_end))
else:
    print("No solution found.")