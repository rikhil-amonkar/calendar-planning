from z3 import Solver, Int, Or, sat

# Meeting parameters:
duration = 60  # meeting duration in minutes (1 hour)
start = Int("start")  # meeting start time (in minutes from midnight)

# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
WORK_START = 540
WORK_END = 1020

# Busy schedules (times in minutes from midnight)

# Bobby's busy schedule:
# Monday:
#   9:30 to 10:00  -> (570, 600)
#   13:30 to 14:30 -> (810, 870)
# Tuesday:
#   9:00 to 9:30   -> (540, 570)
bobby_busy = {
    0: [(570, 600), (810, 870)],
    1: [(540, 570)]
}

# Jason's busy schedule:
# Monday:
#   9:00 to 10:00   -> (540, 600)
#   11:00 to 12:30  -> (660, 750)
#   13:00 to 13:30  -> (780, 810)
#   14:00 to 17:00  -> (840, 1020)
# Tuesday:
#   9:00 to 14:30   -> (540, 870)
#   15:00 to 16:00  -> (900, 960)
#   16:30 to 17:00  -> (990, 1020)
jason_busy = {
    0: [(540, 600), (660, 750), (780, 810), (840, 1020)],
    1: [(540, 870), (900, 960), (990, 1020)]
}

# Helper function to ensure that the meeting interval [start, start+duration)
# does not overlap with a given busy interval [busy_start, busy_end).
def non_overlap(busy_start, busy_end):
    return Or(start + duration <= busy_start, start >= busy_end)

found = False
meeting_day = None   # 0 for Monday, 1 for Tuesday
meeting_start = None

# Try scheduling on Monday (day 0) and Tuesday (day 1)
for day in [0, 1]:
    solver = Solver()
    
    # Constrain meeting to be within work hours.
    solver.add(start >= WORK_START, start + duration <= WORK_END)
    
    # Add Bobby's busy intervals constraints.
    for b_start, b_end in bobby_busy.get(day, []):
        solver.add(non_overlap(b_start, b_end))
        
    # Add Jason's busy intervals constraints.
    for b_start, b_end in jason_busy.get(day, []):
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
    # Format output into HH:MM.
    start_hr, start_min = divmod(meeting_start, 60)
    end_hr, end_min = divmod(meeting_end, 60)
    day_str = "Monday" if meeting_day == 0 else "Tuesday"
    print(f"A valid meeting time is on {day_str} from {start_hr:02d}:{start_min:02d} to {end_hr:02d}:{end_min:02d}.")
else:
    print("No valid meeting time could be found that meets all constraints.")