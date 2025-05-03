from z3 import Solver, Int, Or, sat

# Meeting parameters:
duration = 60  # meeting duration in minutes (1 hour)
start = Int("start")  # meeting start time in minutes from midnight

# Work hours: from 9:00 (540 minutes) to 17:00 (1020 minutes)
WORK_START = 540
WORK_END = 1020

# Busy schedules (all times in minutes from midnight):

# Benjamin's busy schedule:
# Monday:
#   14:00 to 15:00 -> (840, 900)
# Tuesday:
#   (None specified)
benjamin_busy = {
    0: [(840, 900)],
    1: []
}

# Cheryl's busy schedule:
# Monday:
#   10:00 to 10:30 -> (600, 630)
#   11:00 to 11:30 -> (660, 690)
#   12:30 to 13:30 -> (750, 810)
#   14:00 to 15:30 -> (840, 930)
#   16:00 to 16:30 -> (960, 990)
# Tuesday:
#   9:30 to 11:30  -> (570, 690)
#   12:00 to 17:00 -> (720, 1020)
cheryl_busy = {
    0: [(600, 630), (660, 690), (750, 810), (840, 930), (960, 990)],
    1: [(570, 690), (720, 1020)]
}

# Additional constraint:
# Benjamin cannot meet on Monday after 10:30.
# Meaning that if the meeting is on Monday (day 0) the meeting must start before 10:30 (i.e., before 630 minutes)

# Helper: ensure that the meeting interval [start, start+duration) does not overlap with a busy interval [busy_start, busy_end)
def non_overlap(busy_start, busy_end):
    return Or(start + duration <= busy_start, start >= busy_end)

found = False
meeting_day = None  # 0 for Monday, 1 for Tuesday
meeting_start = None

# We try to schedule on Monday first, then Tuesday.
for day in [0, 1]:
    solver = Solver()
    # Meeting must be within work hours.
    solver.add(start >= WORK_START, start + duration <= WORK_END)
    
    # Add additional constraint for Benjamin on Monday:
    if day == 0:
        solver.add(start < 630)  # Meeting must start before 10:30 on Monday
    
    # Add busy constraints for Benjamin.
    for (busy_start, busy_end) in benjamin_busy.get(day, []):
        solver.add(non_overlap(busy_start, busy_end))
        
    # Add busy constraints for Cheryl.
    for (busy_start, busy_end) in cheryl_busy.get(day, []):
        solver.add(non_overlap(busy_start, busy_end))
    
    # Try possible meeting start times (minute by minute)
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
    start_hour, start_min = divmod(meeting_start, 60)
    end_hour, end_min = divmod(meeting_end, 60)
    day_str = "Monday" if meeting_day == 0 else "Tuesday"
    print(f"A valid meeting time is on {day_str} from {start_hour:02d}:{start_min:02d} to {end_hour:02d}:{end_min:02d}.")
else:
    print("No valid meeting time could be found that meets all constraints.")