from z3 import Solver, Int, Or, sat

# Meeting parameters:
duration = 60  # meeting duration in minutes (1 hour)
start = Int("start")  # meeting start time in minutes from midnight

# Work hours: from 9:00 (540 minutes) to 17:00 (1020 minutes)
WORK_START = 540
WORK_END = 1020

# Busy schedules (times are in minutes from midnight):

# Roger's busy schedule:
# Monday:
#   11:00 to 11:30 -> (660, 690)
#   12:30 to 13:30 -> (750, 810)
# Tuesday:
#   12:30 to 13:00 -> (750, 780)
roger_busy = {
    0: [(660, 690), (750, 810)],
    1: [(750, 780)]
}

# Logan's busy schedule:
# Monday:
#   9:00 to 9:30  -> (540, 570)
#   10:00 to 13:00 -> (600, 780)
#   13:30 to 16:00 -> (810, 960)
# Tuesday:
#   9:00 to 14:00  -> (540, 840)
#   15:00 to 15:30 -> (900, 930)
#   16:00 to 16:30 -> (960, 990)
logan_busy = {
    0: [(540, 570), (600, 780), (810, 960)],
    1: [(540, 840), (900, 930), (960, 990)]
}

# Roger's preference: he would like to avoid more meetings on Monday.
# To honor this preference, we try Tuesday first, and only if no solution is
# found for Tuesday, we try Monday.

# Helper function:
# The meeting interval [start, start+duration) should not overlap with a busy interval [busy_start, busy_end)
def non_overlap(busy_start, busy_end):
    return Or(start + duration <= busy_start, start >= busy_end)

found = False
meeting_day = None  # 0 for Monday, 1 for Tuesday
meeting_start = None

# Try scheduling: try Tuesday (day 1) first, then Monday (day 0)
for day in [1, 0]:
    solver = Solver()
    # Meeting must be within work hours.
    solver.add(start >= WORK_START, start + duration <= WORK_END)
    
    # Add busy constraints for Roger.
    for (busy_start, busy_end) in roger_busy.get(day, []):
        solver.add(non_overlap(busy_start, busy_end))
    
    # Add busy constraints for Logan.
    for (busy_start, busy_end) in logan_busy.get(day, []):
        solver.add(non_overlap(busy_start, busy_end))
    
    # Try each possible start time (minute-by-minute)
    for t in range(WORK_START, WORK_END - duration + 1):
        solver.push()
        solver.add(start == t)
        if solver.check() == sat:
            meeting_start = t
            meeting_day = day
            found = True
            solver.pop()  # Remove the equality constraint before breaking out
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