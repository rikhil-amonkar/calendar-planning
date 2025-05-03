from z3 import Solver, Int, Or, sat

# Meeting parameters:
duration = 60  # meeting duration in minutes (1 hour)
start = Int("start")  # meeting start time in minutes from midnight

# Work hours: from 9:00 (540 minutes) to 17:00 (1020 minutes)
WORK_START = 540
WORK_END = 1020

# Busy schedules (times expressed in minutes from midnight):

# Beverly's busy schedule:
# Monday:
#   14:00 to 14:30 -> (840, 870)
#   15:30 to 16:00 -> (930, 960)
# Tuesday:
#   10:00 to 10:30 -> (600, 630)
#   11:30 to 12:00 -> (690, 720)
beverly_busy = {
    0: [(840, 870), (930, 960)],
    1: [(600, 630), (690, 720)]
}

# Joshua's busy schedule:
# Monday:
#   9:00 to 10:00   -> (540, 600)
#   10:30 to 11:00  -> (630, 660)
#   11:30 to 12:00  -> (690, 720)
#   13:00 to 14:00  -> (780, 840)
#   14:30 to 15:00  -> (870, 900)
#   15:30 to 16:00  -> (930, 960)
# Tuesday:
#   9:00 to 14:00   -> (540, 840)
#   14:30 to 15:30  -> (870, 930)
#   16:00 to 17:00  -> (960, 1020)
joshua_busy = {
    0: [(540, 600), (630, 660), (690, 720), (780, 840), (870, 900), (930, 960)],
    1: [(540, 840), (870, 930), (960, 1020)]
}

# Additional preference:
# Beverly would rather not meet on Monday after 13:00.
# We interpret this as: If the meeting is on Monday (day 0), it must finish by 13:00 (780 minutes).
# Hence, when scheduling on Monday, we force start + duration <= 780.

# Helper: The meeting interval [start, start+duration) must not overlap with a busy interval [busy_start, busy_end)
def non_overlap(busy_start, busy_end):
    return Or(start + duration <= busy_start, start >= busy_end)

found = False
meeting_day = None  # 0 for Monday, 1 for Tuesday
meeting_start = None

# We'll try Monday first, then Tuesday.
for day in [0, 1]:
    solver = Solver()
    # Meeting must be within work hours:
    solver.add(start >= WORK_START, start + duration <= WORK_END)
    
    # If meeting is on Monday, enforce Beverly's preference: meeting must end by 13:00 (780).
    if day == 0:
        solver.add(start + duration <= 780)
        
    # Add Beverly's busy times for the day.
    for b_start, b_end in beverly_busy.get(day, []):
        solver.add(non_overlap(b_start, b_end))
    
    # Add Joshua's busy times for the day.
    for b_start, b_end in joshua_busy.get(day, []):
        solver.add(non_overlap(b_start, b_end))
    
    # Search minute-by-minute for a valid start time.
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