from z3 import Solver, Int, Or, sat

# Meeting parameters:
duration = 30  # meeting duration in minutes
start = Int("start")  # meeting start time in minutes from midnight

# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
WORK_START = 540
WORK_END = 1020

# Charlotte's busy schedule (times in minutes from midnight)
# Monday (day 0):
#   9:00 to 11:00   -> (540, 660)
#   12:00 to 12:30  -> (720, 750)
#   13:30 to 14:00  -> (810, 840)
#   14:30 to 16:30  -> (870, 990)
#
# Tuesday (day 1):
#   9:30 to 10:30   -> (570, 630)
#   11:30 to 12:30  -> (690, 750)
#   13:30 to 16:00  -> (810, 960)
#   16:30 to 17:00  -> (990, 1020)
charlotte_busy = {
    0: [(540, 660), (720, 750), (810, 840), (870, 990)],
    1: [(570, 630), (690, 750), (810, 960), (990, 1020)]
}

# Austin has no constraints (wide open), so we don't need to encode any busy periods.

# Charlotte would rather not meet on Monday.
# We interpret this as a preference to schedule on Tuesday if possible.
# We'll try Tuesday first (day 1), then Monday (day 0) if no slot is found on Tuesday.

# Helper function to ensure the meeting [start, start+duration) does not overlap with a busy interval.
def non_overlap(busy_start, busy_end):
    return Or(start + duration <= busy_start, start >= busy_end)

found = False
meeting_day = None  # 0 for Monday, 1 for Tuesday
meeting_start = None

# Try Tuesday (day 1) first, then Monday (day 0)
for day in [1, 0]:
    solver = Solver()
    # The meeting must be scheduled within work hours
    solver.add(start >= WORK_START, start + duration <= WORK_END)
    
    # Add Charlotte's busy constraints on the current day.
    for b_start, b_end in charlotte_busy.get(day, []):
        solver.add(non_overlap(b_start, b_end))
    
    # Iterate over possible start times in ascending order (earliest availability)
    for t in range(WORK_START, WORK_END - duration + 1):
        solver.push()
        solver.add(start == t)
        if solver.check() == sat:
            meeting_start = t
            meeting_day = day
            found = True
            solver.pop()  # Clean the temporary choice
            break
        solver.pop()
    if found:
        break

if found:
    meeting_end = meeting_start + duration
    # Convert minutes into HH:MM format.
    start_hour, start_min = divmod(meeting_start, 60)
    end_hour, end_min = divmod(meeting_end, 60)
    day_str = "Monday" if meeting_day == 0 else "Tuesday"
    print(f"A valid meeting time is on {day_str} from {start_hour:02d}:{start_min:02d} to {end_hour:02d}:{end_min:02d}.")
else:
    print("No valid meeting time could be found that meets all constraints.")