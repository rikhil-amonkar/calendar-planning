from z3 import Solver, Int, Or, sat

# Meeting parameters:
duration = 60  # meeting duration in minutes (1 hour)
start = Int("start")  # meeting start time in minutes from midnight

# Work hours: from 9:00 (540) to 17:00 (1020)
WORK_START = 540
WORK_END = 1020

# Busy schedules (times are in minutes from midnight):

# Diana's busy schedule: (None, she is free the whole week)
diana_busy = {
    0: [],  # Monday
    1: []   # Tuesday
}

# Samantha's busy schedule:
# Monday:
#   9:30 to 10:30 -> (570, 630)
#   11:30 to 12:30 -> (690, 750)
#   13:00 to 15:00 -> (780, 900)
#   15:30 to 16:00 -> (930, 960)
# Tuesday:
#   9:00 to 9:30   -> (540, 570)
#   10:00 to 10:30 -> (600, 630)
#   11:00 to 11:30 -> (660, 690)
#   13:00 to 13:30 -> (780, 810)
#   14:30 to 17:00 -> (870, 1020)
samantha_busy = {
    0: [(570, 630), (690, 750), (780, 900), (930, 960)],
    1: [(540, 570), (600, 630), (660, 690), (780, 810), (870, 1020)]
}

# Additional constraints:
# 1. Diana cannot meet on Tuesday.
# 2. Samantha does not want to meet on Monday after 14:30 (i.e., meeting must start before 14:30, which is 14*60+30=870 minutes).

# Helper function: meeting [start, start+duration) should not overlap a busy interval [busy_start, busy_end)
def non_overlap(busy_start, busy_end):
    return Or(start + duration <= busy_start, start >= busy_end)

found = False
meeting_day = None  # 0 for Monday, 1 for Tuesday
meeting_start = None

# Try scheduling on each day. We'll check Monday first, then Tuesday.
for day in [0, 1]:
    solver = Solver()
    # The meeting must be scheduled within the working hours.
    solver.add(start >= WORK_START, start + duration <= WORK_END)
    
    # Day-specific additional constraints:
    if day == 0:
        # Samantha does not want meetings on Monday after 14:30,
        # so meeting must start before 14:30 (i.e., before 870 minutes).
        solver.add(start < 870)
    if day == 1:
        # Diana cannot meet on Tuesday.
        solver.add(False)
    
    # Add busy constraints for Diana (none in this case, but for uniformity):
    for (busy_start, busy_end) in diana_busy.get(day, []):
        solver.add(non_overlap(busy_start, busy_end))
        
    # Add busy constraints for Samantha.
    for (busy_start, busy_end) in samantha_busy.get(day, []):
        solver.add(non_overlap(busy_start, busy_end))
    
    # Iterate over possible meeting start times (minute by minute)
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