from z3 import Solver, Int, Or, sat

# Meeting parameters:
duration = 30  # meeting duration in minutes (half an hour)
start = Int("start")  # meeting start time in minutes from midnight

# Work hours: from 9:00 (540 minutes) to 17:00 (1020 minutes)
WORK_START = 540
WORK_END = 1020

# Busy schedules (all times in minutes from midnight):

# Matthew's busy schedule:
# Monday:
#   9:00 to 9:30  -> (540, 570)
#   14:00 to 15:00 -> (840, 900)
#   16:30 to 17:00 -> (990, 1020)
# Tuesday:
#   12:30 to 13:30 -> (750, 810)
#   14:00 to 14:30 -> (840, 870)
#   15:30 to 16:00 -> (930, 960)
matthew_busy = {
    0: [(540, 570), (840, 900), (990, 1020)],
    1: [(750, 810), (840, 870), (930, 960)]
}

# Jennifer's busy schedule:
# Monday:
#   10:30 to 11:30 -> (630, 690)
#   12:30 to 14:00 -> (750, 840)
#   15:00 to 15:30 -> (900, 930)
#   16:00 to 17:00 -> (960, 1020)
# Tuesday:
#   9:00 to 9:30   -> (540, 570)
#   11:30 to 12:00 -> (690, 720)
#   13:00 to 13:30 -> (780, 810)
#   14:00 to 15:30 -> (840, 930)
#   16:00 to 17:00 -> (960, 1020)
jennifer_busy = {
    0: [(630, 690), (750, 840), (900, 930), (960, 1020)],
    1: [(540, 570), (690, 720), (780, 810), (840, 930), (960, 1020)]
}

# Additional preferences:
# - Matthew would rather not meet on Monday. We'll try Tuesday first.
# - Jennifer cannot meet on Tuesday before 13:00 (i.e., meeting must start at or after 13:00, which is 780 minutes).

# Helper function:
# The meeting interval [start, start+duration) must not overlap with a busy interval [busy_start, busy_end)
def non_overlap(busy_start, busy_end):
    return Or(start + duration <= busy_start, start >= busy_end)

found = False
meeting_day = None  # 0 for Monday, 1 for Tuesday
meeting_start = None

# We'll try Tuesday first (day 1), then Monday (day 0)
for day in [1, 0]:
    solver = Solver()
    
    # Meeting must be within the work hours.
    solver.add(start >= WORK_START, start + duration <= WORK_END)

    # Apply additional constraints based on the day:
    if day == 1:
        # For Tuesday, Jennifer cannot meet before 13:00
        solver.add(start >= 780)
    
    # Add busy schedule constraints for Matthew.
    for b_start, b_end in matthew_busy.get(day, []):
        solver.add(non_overlap(b_start, b_end))
    
    # Add busy schedule constraints for Jennifer.
    for b_start, b_end in jennifer_busy.get(day, []):
        solver.add(non_overlap(b_start, b_end))
    
    # Enumerate possible start times minute-by-minute.
    for t in range(WORK_START, WORK_END - duration + 1):
        solver.push()
        solver.add(start == t)
        if solver.check() == sat:
            meeting_start = t
            meeting_day = day
            found = True
            solver.pop()  # remove the equality constraint before breaking out
            break
        solver.pop()
    
    if found:
        break

if found:
    meeting_end = meeting_start + duration
    sh, sm = divmod(meeting_start, 60)
    eh, em = divmod(meeting_end, 60)
    day_str = "Monday" if meeting_day == 0 else "Tuesday"
    print(f"A valid meeting time is on {day_str} from {sh:02d}:{sm:02d} to {eh:02d}:{em:02d}.")
else:
    print("No valid meeting time could be found that meets all constraints.")