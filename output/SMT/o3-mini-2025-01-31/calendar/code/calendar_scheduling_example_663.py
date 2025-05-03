from z3 import Solver, Int, Or, sat

# Meeting parameters:
duration = 30  # meeting duration in minutes (half an hour)
start = Int("start")  # meeting start time in minutes from midnight

# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
WORK_START = 540
WORK_END = 1020

# Busy schedules (all times in minutes from midnight):

# Jordan has no meetings the entire week.
jordan_busy = {
    0: [],  # Monday
    1: []   # Tuesday
}

# Amber's busy schedule:
# Monday:
#   9:00 to 11:30 -> (540, 690)
#   12:30 to 13:00 -> (750, 780)
#   15:00 to 15:30 -> (900, 930)
#   16:00 to 17:00 -> (960, 1020)
# Tuesday:
#   10:30 to 11:30 -> (630, 690)
#   12:00 to 12:30 -> (720, 750)
#   13:30 to 14:00 -> (810, 840)
#   14:30 to 15:00 -> (870, 900)
#   15:30 to 16:00 -> (930, 960)
#   16:30 to 17:00 -> (990, 1020)
amber_busy = {
    0: [(540, 690), (750, 780), (900, 930), (960, 1020)],
    1: [(630, 690), (720, 750), (810, 840), (870, 900), (930, 960), (990, 1020)]
}

# Additional constraints (preferences):
# 1. Jordan does not want to meet on Monday.
# 2. On Tuesday, Jordan does not want the meeting to extend after 12:00.
#    (i.e., if meeting is on Tuesday, it must finish by 12:00,
#     so start + duration <= 720).

# Helper function: the meeting interval [start, start+duration)
# should not overlap with a busy interval [busy_start, busy_end).
def non_overlap(busy_start, busy_end):
    return Or(start + duration <= busy_start, start >= busy_end)

found = False
meeting_day = None  # 0 for Monday, 1 for Tuesday
meeting_start = None

# Try scheduling for each day.
# We try Monday first, then Tuesday.
for day in [0, 1]:
    solver = Solver()
    
    # The meeting must be within work hours.
    solver.add(start >= WORK_START, start + duration <= WORK_END)
    
    # Add the personal scheduling constraints:
    if day == 0:
        # Jordan does not want to meet on Monday.
        solver.add(False)
    if day == 1:
        # On Tuesday, the meeting must finish by 12:00.
        solver.add(start + duration <= 720)
    
    # Add busy constraints for Jordan (none in this case).
    for (busy_start, busy_end) in jordan_busy.get(day, []):
        solver.add(non_overlap(busy_start, busy_end))
    
    # Add busy constraints for Amber.
    for (busy_start, busy_end) in amber_busy.get(day, []):
        solver.add(non_overlap(busy_start, busy_end))
    
    # Try possible meeting start times, minute-by-minute.
    for t in range(WORK_START, WORK_END - duration + 1):
        solver.push()
        solver.add(start == t)
        if solver.check() == sat:
            meeting_start = t
            meeting_day = day
            found = True
            solver.pop()  # Remove the equality constraint.
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