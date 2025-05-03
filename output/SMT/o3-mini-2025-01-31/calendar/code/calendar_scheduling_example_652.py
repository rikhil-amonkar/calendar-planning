from z3 import Solver, Int, Or, sat

# Meeting parameters:
duration = 30  # meeting duration is 30 minutes
start = Int("start")  # meeting start time in minutes from midnight

# Work hours: from 9:00 (540 minutes) to 17:00 (1020 minutes)
WORK_START = 540
WORK_END = 1020

# Busy schedules represented as lists of (busy_start, busy_end) in minutes:

# Jesse's busy schedule:
# Monday:
#   13:30 to 14:00 -> (810, 840)
#   14:30 to 15:00 -> (870, 900)
# Tuesday:
#   9:00 to 9:30   -> (540, 570)
#   13:00 to 13:30 -> (780, 810)
#   14:00 to 15:00 -> (840, 900)
jesse_busy = {
    0: [(810, 840), (870, 900)],
    1: [(540, 570), (780, 810), (840, 900)]
}

# Lawrence's busy schedule:
# Monday:
#   Busy the whole day from 9:00 to 17:00 -> (540, 1020)
# Tuesday:
#   9:30 to 10:30  -> (570, 630)
#   11:30 to 12:30 -> (690, 750)
#   13:00 to 13:30 -> (780, 810)
#   14:30 to 15:00 -> (870, 900)
#   15:30 to 16:30 -> (930, 990)
lawrence_busy = {
    0: [(540, 1020)],  # fully busy on Monday
    1: [(570, 630), (690, 750), (780, 810), (870, 900), (930, 990)]
}

# Additional constraint:
# "Lawrence can not meet on Tuesday after 16:30."
# That means if the meeting is on Tuesday, the meeting must finish by 16:30 (i.e., start + duration <= 990).

# Helper function that returns a constraint stating the meeting interval [start, start+duration)
# does not overlap with a busy interval [busy_start, busy_end)
def non_overlap(busy_start, busy_end):
    return Or(start + duration <= busy_start, start >= busy_end)

found = False
meeting_day = None  # 0 for Monday, 1 for Tuesday
meeting_start = None

# We want the earliest availability.
# Try Monday first (day 0), then Tuesday (day 1) if needed.
for day_val in [0, 1]:
    solver = Solver()
    # The meeting must be within the work hours.
    solver.add(start >= WORK_START, start + duration <= WORK_END)
    
    # If it's Tuesday, add the extra constraint for Lawrence's Tuesday availability.
    if day_val == 1:
        solver.add(start + duration <= 990)  # Must finish by 16:30 (990 minutes)
    
    # Add Jesse's busy constraints.
    for (busy_start, busy_end) in jesse_busy.get(day_val, []):
        solver.add(non_overlap(busy_start, busy_end))
    
    # Add Lawrence's busy constraints.
    for (busy_start, busy_end) in lawrence_busy.get(day_val, []):
        solver.add(non_overlap(busy_start, busy_end))
    
    # Try possible start times (minute by minute) from WORK_START to latest start time.
    for t in range(WORK_START, WORK_END - duration + 1):
        solver.push()  # save state
        solver.add(start == t)
        if solver.check() == sat:
            meeting_start = t
            meeting_day = day_val
            found = True
            solver.pop()
            break
        solver.pop()
    if found:
        break

if found:
    meeting_end = meeting_start + duration
    start_hour, start_min = divmod(meeting_start, 60)
    end_hour, end_min = divmod(meeting_end, 60)
    day_str = "Monday" if meeting_day == 0 else "Tuesday"
    print(f"A valid meeting time is on {day_str} from {start_hour:02d}:{start_min:02d} to {end_hour:02d}:{end_min:02d}.")
else:
    print("No valid meeting time could be found that meets all constraints.")