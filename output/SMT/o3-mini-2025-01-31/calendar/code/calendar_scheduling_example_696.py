from z3 import Solver, Int, Or, sat

# Meeting parameters:
duration = 60  # meeting duration in minutes (one hour)
start = Int("start")  # meeting start time in minutes from midnight

# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
WORK_START = 540
WORK_END = 1020

# Busy schedules for each participant on Monday (day 0) and Tuesday (day 1)

# Roy's busy schedule in minutes (from midnight)
# Monday:
#   9:30 to 10:00  -> (570, 600)
#   14:30 to 15:30 -> (870, 930)
#   16:00 to 16:30 -> (960, 990)
# Tuesday:
#   9:00 to 9:30   -> (540, 570)
#   13:00 to 13:30 -> (780, 810)
roy_busy = {
    0: [(570, 600), (870, 930), (960, 990)],
    1: [(540, 570), (780, 810)]
}

# Anna's busy schedule in minutes
# Monday:
#   9:00 to 9:30   -> (540, 570)
#   10:00 to 11:30 -> (600, 690)
#   12:00 to 12:30 -> (720, 750)
#   13:00 to 13:30 -> (780, 810)
#   14:00 to 15:00 -> (840, 900)
#   15:30 to 16:30 -> (930, 990)
# Tuesday:
#   9:00 to 15:30  -> (540, 930)
#   16:30 to 17:00 -> (990, 1020)
anna_busy = {
    0: [(540, 570), (600, 690), (720, 750), (780, 810), (840, 900), (930, 990)],
    1: [(540, 930), (990, 1020)]
}

# Helper function to ensure that the meeting interval [start, start+duration)
# does not overlap with a busy interval [busy_start, busy_end)
def non_overlap(busy_start, busy_end):
    return Or(start + duration <= busy_start, start >= busy_end)

found = False
meeting_day = None  # 0 for Monday, 1 for Tuesday
meeting_start = None

# We'll check days in the order Tuesday first, then Monday.
for day in [1, 0]:
    solver = Solver()
    
    # The meeting must lie within work hours.
    solver.add(start >= WORK_START, start + duration <= WORK_END)
    
    # Add constraints from Roy's busy intervals for the given day.
    for b_start, b_end in roy_busy.get(day, []):
        solver.add(non_overlap(b_start, b_end))
        
    # Add constraints from Anna's busy intervals for the given day.
    for b_start, b_end in anna_busy.get(day, []):
        solver.add(non_overlap(b_start, b_end))
        
    # Iterate over possible start times in ascending order.
    for t in range(WORK_START, WORK_END - duration + 1):
        solver.push()
        solver.add(start == t)
        if solver.check() == sat:
            meeting_start = t
            meeting_day = day
            found = True
            solver.pop()  # remove the temporary assignment for t
            break
        solver.pop()
    
    if found:
        break

if found:
    meeting_end = meeting_start + duration
    # Convert minutes to HH:MM format.
    start_hour, start_min = divmod(meeting_start, 60)
    end_hour, end_min = divmod(meeting_end, 60)
    day_str = "Monday" if meeting_day == 0 else "Tuesday"
    print(f"A valid meeting time is on {day_str} from {start_hour:02d}:{start_min:02d} to {end_hour:02d}:{end_min:02d}.")
else:
    print("No valid meeting time could be found that meets all constraints.")