from z3 import Solver, Int, Or, sat

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters.
duration = 30  # meeting duration in minutes (half an hour)
start = Int("start")  # meeting start time in minutes since midnight
day = Int("day")      # 0 for Monday, 1 for Tuesday

# The meeting must occur on either Monday (0) or Tuesday (1)
solver.add(Or(day == 0, day == 1))

# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
solver.add(start >= 540, start + duration <= 1020)

# ------------------------------------------------------------------
# In this problem, Jessica is busy all day on Monday (9:00-17:00)
# so the meeting can only happen on Tuesday.
solver.add(day == 1)
# ------------------------------------------------------------------

# Define a helper to add busy constraints given a list of (b_start, b_end) intervals.
# The meeting interval [start, start + duration) must not overlap with the busy interval.
def add_busy_intervals(solver, busy_intervals):
    for b_start, b_end in busy_intervals:
        solver.add(Or(start + duration <= b_start, start >= b_end))

# Bruce's busy intervals:
# Monday intervals (day==0): 9:30-10:00, 11:00-11:30, 12:00-12:30, 13:30-14:00, 14:30-15:00, 16:00-16:30
bruce_monday_busy = [
    (570, 600),
    (660, 690),
    (720, 750),
    (810, 840),
    (870, 900),
    (960, 990)
]

# Tuesday intervals (day==1): 12:00-12:30, 13:30-14:00
bruce_tuesday_busy = [
    (720, 750),
    (810, 840)
]

# Jessica's busy intervals:
# Monday intervals (day==0): 9:00-17:00 (effectively the entire day, so meeting is impossible)
jessica_monday_busy = [
    (540, 1020)
]
# Tuesday intervals (day==1): 9:30-12:30, 13:00-17:00
jessica_tuesday_busy = [
    (570, 750),
    (780, 1020)
]

# Since we forced meeting to be on Tuesday (day == 1), add Tuesday constraints:
# For Bruce on Tuesday:
add_busy_intervals(solver, bruce_tuesday_busy)
# For Jessica on Tuesday:
# For Jessica, ensure the meeting does not overlap with either busy block.
# For the block 9:30-12:30: meeting must end by 9:30 or start at/after 12:30.
solver.add(Or(start + duration <= 570, start >= 750))
# For the block 13:00-17:00: meeting must end by 13:00 (780) because a meeting starting later would
# go beyond work hours.
solver.add(start + duration <= 780)

# Search for the earliest valid meeting time.
found = False
# Given Jessica's second constraint (start + duration <= 780), the latest starting time is 780 - 30 = 750.
for t in range(540, 751):
    solver.push()
    solver.add(start == t)
    if solver.check() == sat:
        meeting_start = t
        meeting_end = t + duration
        # Since day==1 corresponds to Tuesday:
        day_string = "Tuesday"
        sh, sm = divmod(meeting_start, 60)
        eh, em = divmod(meeting_end, 60)
        print(f"A valid meeting time is on {day_string} from {sh:02d}:{sm:02d} to {eh:02d}:{em:02d}.")
        found = True
        solver.pop()
        break
    solver.pop()

if not found:
    print("No valid meeting time could be found.")