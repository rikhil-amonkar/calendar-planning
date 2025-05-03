from z3 import Solver, Int, Or, sat

# Meeting parameters:
duration = 30  # duration in minutes (half an hour)
start = Int("start")  # meeting start time in minutes from midnight

# Work hours (in minutes from midnight): 9:00 (540) to 17:00 (1020)
WORK_START = 540
WORK_END = 1020

# Busy schedules for each participant in minutes from midnight

# Adam's busy schedule:
# Monday:
#    15:30 to 16:30 -> (930, 990)
# Tuesday:
#    (no meetings)
adam_busy = {
    0: [(930, 990)],
    1: []
}

# Martha's busy schedule:
# Monday:
#    9:30 to 11:00 -> (570, 660)
#    11:30 to 14:00 -> (690, 840)
#    14:30 to 16:00 -> (870, 960)
# Tuesday:
#    9:00 to 9:30   -> (540, 570)
#    10:00 to 10:30 -> (600, 630)
#    11:00 to 14:00 -> (660, 840)
#    15:00 to 15:30 -> (900, 930)
#    16:00 to 17:00 -> (960, 1020)
martha_busy = {
    0: [(570, 660), (690, 840), (870, 960)],
    1: [(540, 570), (600, 630), (660, 840), (900, 930), (960, 1020)]
}

# Additional participant constraints:
# Adam would rather not meet on Monday.
# Martha would rather not meet on Tuesday before 15:00 (i.e. before 900 minutes).

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
    # Meeting must be within work hours.
    solver.add(start >= WORK_START, start + duration <= WORK_END)
    
    # Add day-specific constraints:
    if day == 0:
        # Adam would rather not meet on Monday.
        solver.add(False)
    elif day == 1:
        # Martha would rather not meet on Tuesday before 15:00.
        solver.add(start >= 900)
    
    # Add Adam's busy intervals for the day.
    for b_start, b_end in adam_busy.get(day, []):
        solver.add(non_overlap(b_start, b_end))
    
    # Add Martha's busy intervals for the day.
    for b_start, b_end in martha_busy.get(day, []):
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