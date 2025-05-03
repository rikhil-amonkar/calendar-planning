from z3 import Solver, Int, Or, sat

# Meeting parameters:
duration = 60  # meeting duration in minutes (1 hour)
start = Int("start")  # meeting start time in minutes from midnight

# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
WORK_START = 540
WORK_END = 1020

# Busy schedules (times in minutes from midnight)

# Hannah's busy schedule:
# Monday:
#   9:30 to 10:30   -> (570, 630)
#   11:30 to 12:30  -> (690, 750)
#   13:30 to 14:00  -> (810, 840)
#   15:00 to 15:30  -> (900, 930)
#   16:00 to 17:00  -> (960, 1020)
# Tuesday:
#   11:00 to 11:30  -> (660, 690)
#   12:30 to 14:00  -> (750, 840)
#   15:00 to 15:30  -> (900, 930)
#   16:30 to 17:00  -> (990, 1020)
hannah_busy = {
    0: [(570, 630), (690, 750), (810, 840), (900, 930), (960, 1020)],
    1: [(660, 690), (750, 840), (900, 930), (990, 1020)]
}

# Steven's busy schedule:
# Monday:
#   9:30 to 12:30   -> (570, 750)
#   13:00 to 14:30  -> (780, 870)
#   15:00 to 17:00  -> (900, 1020)
# Tuesday:
#   9:00 to 10:30   -> (540, 630)
#   11:00 to 12:00  -> (660, 720)
#   12:30 to 13:00  -> (750, 780)
#   13:30 to 14:00  -> (810, 840)
#   15:30 to 16:00  -> (930, 960)
#   16:30 to 17:00  -> (990, 1020)
steven_busy = {
    0: [(570, 750), (780, 870), (900, 1020)],
    1: [(540, 630), (660, 720), (750, 780), (810, 840), (930, 960), (990, 1020)]
}

# Helper function to ensure that the meeting interval [start, start+duration)
# does not overlap with an existing busy interval [busy_start, busy_end)
def non_overlap(busy_start, busy_end):
    return Or(start + duration <= busy_start, start >= busy_end)

found = False
meeting_day = None  # 0 for Monday, 1 for Tuesday
meeting_start = None

# We check Monday first, then Tuesday (earliest availability)
for day in [0, 1]:
    solver = Solver()
    # Constraint: meeting must be within work hours
    solver.add(start >= WORK_START, start + duration <= WORK_END)
    
    # Add Hannah's busy intervals for the day
    for b_start, b_end in hannah_busy.get(day, []):
        solver.add(non_overlap(b_start, b_end))
    
    # Add Steven's busy intervals for the day
    for b_start, b_end in steven_busy.get(day, []):
        solver.add(non_overlap(b_start, b_end))
    
    # Try possible start times in ascending order (earlier times first)
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
    # Convert minutes to HH:MM format
    start_hour, start_min = divmod(meeting_start, 60)
    end_hour, end_min = divmod(meeting_end, 60)
    day_str = "Monday" if meeting_day == 0 else "Tuesday"
    print(f"A valid meeting time is on {day_str} from {start_hour:02d}:{start_min:02d} to {end_hour:02d}:{end_min:02d}.")
else:
    print("No valid meeting time could be found that meets all constraints.")