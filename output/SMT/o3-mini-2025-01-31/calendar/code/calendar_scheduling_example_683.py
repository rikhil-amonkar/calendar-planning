from z3 import Solver, Int, Or, sat

# Meeting parameters:
duration = 30  # meeting duration in minutes (half an hour)
start = Int("start")  # meeting start time in minutes from midnight

# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
WORK_START = 540
WORK_END = 1020

# Busy schedules (times in minutes from midnight)

# Judith is free the entire week, so no busy intervals.
judith_busy = {
    0: [],  # Monday
    1: []   # Tuesday
}

# Gary's busy schedule:
# Monday:
#   10:00 to 10:30 -> (600, 630)
#   12:00 to 12:30 -> (720, 750)
#   13:00 to 15:00 -> (780, 900)
#   15:30 to 17:00 -> (930, 1020)
# Tuesday:
#   9:00 to 12:30   -> (540, 750)
#   13:00 to 14:00  -> (780, 840)
#   14:30 to 16:00  -> (870, 960)
#   16:30 to 17:00  -> (990, 1020)
gary_busy = {
    0: [(600, 630), (720, 750), (780, 900), (930, 1020)],
    1: [(540, 750), (780, 840), (870, 960), (990, 1020)]
}

# Additional user preferences:
# - Gary does not want to meet on Monday.
# - Judith would like to avoid meetings on Tuesday after 15:30.
#   For Tuesday, we interpret this as the meeting must end by 15:30, i.e.,
#   start + duration <= 15:30, which in minutes is 930.

# Helper function that ensures the meeting interval [start, start+duration)
# does not overlap with a given busy interval [busy_start, busy_end).
def non_overlap(busy_start, busy_end):
    return Or(start + duration <= busy_start, start >= busy_end)

found = False
meeting_day = None  # 0 for Monday, 1 for Tuesday
meeting_start = None

# Try scheduling on Monday (day 0) and Tuesday (day 1)
for day in [0, 1]:
    solver = Solver()
    # Constrain the meeting to be within work hours.
    solver.add(start >= WORK_START, start + duration <= WORK_END)
    
    # Add day-specific constraints:
    if day == 0:
        # Gary does not want to meet on Monday.
        solver.add(False)
    elif day == 1:
        # Judith would like to avoid meetings after 15:30.
        # Meeting must finish by 15:30, i.e., start + duration <= 930.
        solver.add(start + duration <= 930)
    
    # Add Judith's busy intervals for the day.
    for b_start, b_end in judith_busy.get(day, []):
        solver.add(non_overlap(b_start, b_end))
    
    # Add Gary's busy intervals for the day.
    for b_start, b_end in gary_busy.get(day, []):
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
    # Convert minutes to HH:MM format.
    start_hr, start_min = divmod(meeting_start, 60)
    end_hr, end_min = divmod(meeting_end, 60)
    day_str = "Monday" if meeting_day == 0 else "Tuesday"
    print(f"A valid meeting time is on {day_str} from {start_hr:02d}:{start_min:02d} to {end_hr:02d}:{end_min:02d}.")
else:
    print("No valid meeting time could be found that meets all constraints.")