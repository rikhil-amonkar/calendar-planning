from z3 import Solver, Int, Or, sat

# Meeting parameters:
duration = 60  # meeting duration in minutes (1 hour)
start = Int("start")  # meeting start time in minutes from midnight

# Work hours: from 9:00 (540 minutes) to 17:00 (1020 minutes)
WORK_START = 540
WORK_END = 1020

# Busy schedules (times in minutes from midnight):

# Sophia's busy schedule:
# Monday:
#   9:00 to 10:30  -> (540, 630)
#   11:30 to 12:00 -> (690, 720)
#   12:30 to 14:00 -> (750, 840)
#   16:30 to 17:00 -> (990, 1020)
# Tuesday:
#   10:30 to 11:00 -> (630, 660)
#   12:30 to 14:00 -> (750, 840)
#   15:00 to 15:30 -> (900, 930)
#   16:30 to 17:00 -> (990, 1020)
sophia_busy = {
    0: [(540, 630), (690, 720), (750, 840), (990, 1020)],
    1: [(630, 660), (750, 840), (900, 930), (990, 1020)]
}

# Laura's busy schedule:
# Monday:
#   9:30 to 12:00  -> (570, 720)
#   12:30 to 15:00 -> (750, 900)
#   16:30 to 17:00 -> (990, 1020)
# Tuesday:
#   9:00 to 9:30   -> (540, 570)
#   10:00 to 11:00 -> (600, 660)
#   12:00 to 14:00 -> (720, 840)
#   14:30 to 15:00 -> (870, 900)
#   15:30 to 17:00 -> (930, 1020)
laura_busy = {
    0: [(570, 720), (750, 900), (990, 1020)],
    1: [(540, 570), (600, 660), (720, 840), (870, 900), (930, 1020)]
}

# Additional constraint:
# Laura cannot meet on Tuesday.
# This means that we must schedule the meeting on Monday only.
valid_days = [0]  # Monday only

# Helper function:
# The meeting interval [start, start+duration) must not overlap with a busy interval [busy_start, busy_end)
def non_overlap(busy_start, busy_end):
    return Or(start + duration <= busy_start, start >= busy_end)

found = False
meeting_day = None  # 0 for Monday; 1 for Tuesday (if allowed)
meeting_start = None

# Try scheduling on valid days (only Monday in this case)
for day in valid_days:
    solver = Solver()
    
    # Meeting must be within work hours.
    solver.add(start >= WORK_START, start + duration <= WORK_END)
    
    # Add busy constraints for Sophia.
    for (b_start, b_end) in sophia_busy.get(day, []):
        solver.add(non_overlap(b_start, b_end))
    
    # Add busy constraints for Laura.
    for (b_start, b_end) in laura_busy.get(day, []):
        solver.add(non_overlap(b_start, b_end))
    
    # Enumerate possible start times (minute-by-minute)
    for t in range(WORK_START, WORK_END - duration + 1):
        solver.push()
        solver.add(start == t)
        if solver.check() == sat:
            meeting_start = t
            meeting_day = day
            found = True
            solver.pop()  # pop equality constraint
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