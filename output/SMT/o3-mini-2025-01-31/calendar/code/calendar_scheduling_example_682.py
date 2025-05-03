from z3 import Solver, Int, Or, sat

# Meeting parameters:
duration = 30  # meeting duration in minutes (half an hour)
start = Int("start")  # meeting start time in minutes from midnight

# Work hours (in minutes from midnight): 9:00 (540) to 17:00 (1020)
WORK_START = 540
WORK_END = 1020

# Busy schedules (times are in minutes from midnight)

# Amanda's busy schedule:
# Monday:
#   9:00 to 10:30 -> (540, 630)
#   11:00 to 11:30 -> (660, 690)
#   12:30 to 13:00 -> (750, 780)
#   13:30 to 14:00 -> (810, 840)
#   14:30 to 15:00 -> (870, 900)
# Tuesday:
#   9:00 to 9:30   -> (540, 570)
#   10:00 to 10:30 -> (600, 630)
#   11:30 to 12:00 -> (690, 720)
#   13:30 to 14:30 -> (810, 870)
#   15:30 to 16:00 -> (930, 960)
#   16:30 to 17:00 -> (990, 1020)
amanda_busy = {
    0: [(540, 630), (660, 690), (750, 780), (810, 840), (870, 900)],
    1: [(540, 570), (600, 630), (690, 720), (810, 870), (930, 960), (990, 1020)]
}

# Nathan's busy schedule:
# Monday:
#   10:00 to 10:30 -> (600, 630)
#   11:00 to 11:30 -> (660, 690)
#   13:30 to 14:30 -> (810, 870)
#   16:00 to 16:30 -> (960, 990)
# Tuesday:
#   9:00 to 10:30  -> (540, 630)
#   11:00 to 13:00 -> (660, 780)
#   13:30 to 14:00 -> (810, 840)
#   14:30 to 15:30 -> (870, 930)
#   16:00 to 16:30 -> (960, 990)
nathan_busy = {
    0: [(600, 630), (660, 690), (810, 870), (960, 990)],
    1: [(540, 630), (660, 780), (810, 840), (870, 930), (960, 990)]
}

# Additional individual constraints:
# - Amanda does not want to meet on Tuesday after 11:00.
#   We'll interpret that as the meeting (lasting 30 minutes) must finish by 11:00,
#   so if the meeting is on Tuesday, then start must be at most 10:30 (i.e. start + 30 <= 660).
# - Nathan cannot meet on Monday.
    
# Helper function: ensures that the meeting interval [start, start+duration)
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
    
    # Add day-specific participant constraints:
    if day == 0:
        # Nathan cannot meet on Monday.
        solver.add(False)
    elif day == 1:
        # Amanda does not want to meet on Tuesday after 11:00.
        # Meeting must finish by 11:00 (i.e., 660 minutes from midnight)
        solver.add(start + duration <= 660)
    
    # Add Amanda's busy intervals constraints for the given day.
    for b_start, b_end in amanda_busy.get(day, []):
        solver.add(non_overlap(b_start, b_end))
    
    # Add Nathan's busy intervals constraints for the given day.
    for b_start, b_end in nathan_busy.get(day, []):
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
    # Formatting the output as HH:MM.
    start_hr, start_min = divmod(meeting_start, 60)
    end_hr, end_min = divmod(meeting_end, 60)
    day_str = "Monday" if meeting_day == 0 else "Tuesday"
    print(f"A valid meeting time is on {day_str} from {start_hr:02d}:{start_min:02d} to {end_hr:02d}:{end_min:02d}.")
else:
    print("No valid meeting time could be found that meets all constraints.")