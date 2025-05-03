from z3 import Solver, Int, Or, sat

# Meeting parameters:
duration = 60  # meeting duration in minutes (1 hour)
start = Int("start")  # meeting start time expressed in minutes from midnight

# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
WORK_START = 540
WORK_END = 1020

# Busy schedules (times in minutes from midnight)

# Albert's busy schedule:
# Monday:
#   12:30 to 13:00 -> (750, 780)
# Tuesday:
#   11:00 to 12:00 -> (660, 720)
#   13:00 to 13:30 -> (780, 810)
albert_busy = {
    0: [(750, 780)],
    1: [(660, 720), (780, 810)]
}

# George's busy schedule:
# Monday:
#   10:30 to 12:30 -> (630, 750)
#   13:00 to 13:30 -> (780, 810)
#   14:30 to 15:30 -> (870, 930)
#   16:00 to 16:30 -> (960, 990)
# Tuesday:
#   9:00 to 10:00   -> (540, 600)
#   11:00 to 14:30  -> (660, 870)
#   15:30 to 16:00  -> (930, 960)
george_busy = {
    0: [(630, 750), (780, 810), (870, 930), (960, 990)],
    1: [(540, 600), (660, 870), (930, 960)]
}

# Additional constraints:
# - Albert cannot meet on Monday.
# - George does not want to meet on Tuesday before 16:00,
#   meaning for Tuesday the meeting must start at or after 16:00 (960 minutes).

# Helper function: ensures that the meeting interval [start, start+duration)
# does not overlap with a given busy interval [busy_start, busy_end).
def non_overlap(busy_start, busy_end):
    return Or(start + duration <= busy_start, start >= busy_end)

found = False
meeting_day = None   # 0 for Monday, 1 for Tuesday
meeting_start = None

# Try scheduling on Monday (day 0) and Tuesday (day 1)
for day in [0, 1]:
    solver = Solver()
    # Constrain meeting to be within work hours.
    solver.add(start >= WORK_START, start + duration <= WORK_END)
    
    # Add day-specific participant constraints
    if day == 0:
        # Albert cannot meet on Monday.
        solver.add(False)
    elif day == 1:
        # George does not want to meet on Tuesday before 16:00.
        solver.add(start >= 960)
        
    # Add Albert's busy intervals constraints for the day.
    for b_start, b_end in albert_busy.get(day, []):
        solver.add(non_overlap(b_start, b_end))
    
    # Add George's busy intervals constraints for the day.
    for b_start, b_end in george_busy.get(day, []):
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