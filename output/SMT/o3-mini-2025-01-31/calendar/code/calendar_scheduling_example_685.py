from z3 import Solver, Int, Or, sat

# Meeting parameters:
duration = 30  # meeting duration in minutes (half an hour)
start = Int("start")  # meeting start time in minutes from midnight

# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
WORK_START = 540
WORK_END = 1020

# Busy schedules (times in minutes from midnight)

# Billy's busy schedule:
# Monday:
#   12:00 to 12:30 -> (720, 750)
#   13:00 to 13:30 -> (780, 810)
# Tuesday:
#   (no meetings)
billy_busy = {
    0: [(720, 750), (780, 810)],
    1: []
}

# Grace's busy schedule:
# Monday:
#   9:30 to 14:30 -> (570, 870)
#   15:00 to 17:00 -> (900, 1020)
# Tuesday:
#   9:00 to 10:30  -> (540, 630)
#   11:00 to 11:30 -> (660, 690)
#   12:00 to 12:30 -> (720, 750)
#   13:00 to 13:30 -> (780, 810)
#   14:00 to 16:00 -> (840, 960)
grace_busy = {
    0: [(570, 870), (900, 1020)],
    1: [(540, 630), (660, 690), (720, 750), (780, 810), (840, 960)]
}

# Additional participant constraints:
# - Billy does not want to meet on Monday before 10:30 (i.e., before 630 minutes).
# - Grace would like to avoid more meetings on Tuesday.
#   We'll interpret Grace's preference by trying Monday first.
    
# Helper function to ensure that the meeting interval [start, start+duration)
# does not overlap with a given busy interval [busy_start, busy_end).
def non_overlap(busy_start, busy_end):
    return Or(start + duration <= busy_start, start >= busy_end)

found = False
meeting_day = None  # 0 for Monday, 1 for Tuesday
meeting_start = None

# We'll try scheduling on Monday first, then Tuesday.
for day in [0, 1]:
    solver = Solver()
    # Constrain the meeting to be within work hours.
    solver.add(start >= WORK_START, start + duration <= WORK_END)
    
    # Day-specific participant constraints:
    if day == 0:
        # Billy does not want to meet on Monday before 10:30.
        solver.add(start >= 630)
        # Grace prefers to avoid Tuesday, so Monday is preferred.
    # For Tuesday, no extra time constraint is added.
    
    # Add Billy's busy intervals for the day.
    for b_start, b_end in billy_busy.get(day, []):
        solver.add(non_overlap(b_start, b_end))
    
    # Add Grace's busy intervals for the day.
    for b_start, b_end in grace_busy.get(day, []):
        solver.add(non_overlap(b_start, b_end))
    
    # Iterate over possible start times (minute granularity)
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
    # Format minutes to HH:MM.
    start_hr, start_min = divmod(meeting_start, 60)
    end_hr, end_min = divmod(meeting_end, 60)
    day_str = "Monday" if meeting_day == 0 else "Tuesday"
    print(f"A valid meeting time is on {day_str} from {start_hr:02d}:{start_min:02d} to {end_hr:02d}:{end_min:02d}.")
else:
    print("No valid meeting time could be found that meets all constraints.")