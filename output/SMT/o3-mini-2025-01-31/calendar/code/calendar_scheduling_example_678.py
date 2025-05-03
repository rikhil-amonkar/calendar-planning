from z3 import Solver, Int, Or, sat

# Meeting parameters:
duration = 60  # Meeting duration in minutes (1 hour)
start = Int("start")  # Meeting start time in minutes from midnight

# Work hours: from 9:00 (540 minutes) to 17:00 (1020 minutes)
WORK_START = 540
WORK_END = 1020

# Busy schedules (times in minutes from midnight)

# Russell's busy schedule:
# Monday: 10:30 to 11:00 -> (630, 660)
# Tuesday: 13:00 to 13:30 -> (780, 810)
russell_busy = {
    0: [(630, 660)],
    1: [(780, 810)]
}

# Alexander's busy schedule:
# Monday:
#   9:00 to 11:30   -> (540, 690)
#   12:00 to 14:30  -> (720, 870)
#   15:00 to 17:00  -> (900, 1020)
# Tuesday:
#   9:00 to 10:00   -> (540, 600)
#   13:00 to 14:00  -> (780, 840)
#   15:00 to 15:30  -> (900, 930)
#   16:00 to 16:30  -> (960, 990)
alexander_busy = {
    0: [(540, 690), (720, 870), (900, 1020)],
    1: [(540, 600), (780, 840), (900, 930), (960, 990)]
}

# Additional constraint for Russell:
# On Tuesday, Russell would rather not meet before 13:30 (i.e., before 810 minutes).
# So if Tuesday, then start >= 810.

# Helper function to ensure that the meeting (interval [start, start+duration))
# does not overlap with a given busy interval (interval [busy_start, busy_end)).
def non_overlap(busy_start, busy_end):
    return Or(start + duration <= busy_start, start >= busy_end)

found = False
meeting_day = None  # 0 for Monday, 1 for Tuesday
meeting_start = None

# Try both days: Monday (day 0) and Tuesday (day 1)
for day in [0, 1]:
    solver = Solver()
    # Meeting must occur within the work hours.
    solver.add(start >= WORK_START, start + duration <= WORK_END)
    
    # Day specific constraint:
    # For Tuesday, add Russell's preference: meeting should start no earlier than 13:30 (810 minutes)
    if day == 1:
        solver.add(start >= 810)
    
    # Add Russell's busy intervals constraints.
    for interval in russell_busy.get(day, []):
        solver.add(non_overlap(interval[0], interval[1]))
    
    # Add Alexander's busy intervals constraints.
    for interval in alexander_busy.get(day, []):
        solver.add(non_overlap(interval[0], interval[1]))
    
    # Try possible start times (minute granularity)
    for t in range(WORK_START, WORK_END - duration + 1):
        solver.push()
        solver.add(start == t)
        if solver.check() == sat:
            meeting_start = t
            meeting_day = day
            found = True
            solver.pop()
            break
        solver.pop()
    
    if found:
        break

if found:
    meeting_end = meeting_start + duration
    # Convert minutes into HH:MM format.
    start_hr, start_min = divmod(meeting_start, 60)
    end_hr, end_min = divmod(meeting_end, 60)
    day_str = "Monday" if meeting_day == 0 else "Tuesday"
    print(f"A valid meeting time is on {day_str} from {start_hr:02d}:{start_min:02d} to {end_hr:02d}:{end_min:02d}.")
else:
    print("No valid meeting time could be found that meets all constraints.")