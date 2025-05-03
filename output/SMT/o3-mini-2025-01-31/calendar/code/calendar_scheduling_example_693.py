from z3 import Solver, Int, Or, sat

# Meeting parameters:
duration = 30  # meeting duration in minutes (half an hour)
start = Int("start")  # meeting start time in minutes from midnight

# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
WORK_START = 540
WORK_END = 1020

# Kenneth's busy schedule (times in minutes from midnight)
# Monday (day 0):
#   9:00 to 11:00   -> (540, 660)
#   11:30 to 16:30  -> (690, 990)
# Tuesday (day 1):
#   9:00 to 17:00   -> (540, 1020)
kenneth_busy = {
    0: [(540, 660), (690, 990)],
    1: [(540, 1020)]
}

# Keith is free the entire week, except he cannot meet on Monday before 12:00.
# We'll encode Keith's constraint separately for Monday.

# Helper function: ensure meeting [start, start+duration) does not overlap with a given busy interval.
def non_overlap(busy_start, busy_end):
    return Or(start + duration <= busy_start, start >= busy_end)

found = False
meeting_day = None  # 0 for Monday, 1 for Tuesday
meeting_start = None

# We have two days: Monday (0) and Tuesday (1).
# However, Tuesday is completely blocked for Kenneth,
# so we expect the meeting to be scheduled on Monday.
for day in [0, 1]:
    solver = Solver()
    # The meeting must be within work hours.
    solver.add(start >= WORK_START, start + duration <= WORK_END)
    
    # Add Kenneth's busy constraints for the given day.
    for b_start, b_end in kenneth_busy.get(day, []):
        solver.add(non_overlap(b_start, b_end))
    
    # Keith's constraint: on Monday, he cannot meet before 12:00.
    if day == 0:
        solver.add(start >= 720)  # 12:00 is 720 minutes
    
    # Try possible start times in ascending order (earlier times first)
    for t in range(WORK_START, WORK_END - duration + 1):
        solver.push()
        solver.add(start == t)
        if solver.check() == sat:
            meeting_start = t
            meeting_day = day
            found = True
            solver.pop()  # clean up
            break
        solver.pop()
    
    if found:
        break

if found:
    meeting_end = meeting_start + duration
    # Convert minutes to HH:MM format.
    start_hour, start_min = divmod(meeting_start, 60)
    end_hour, end_min = divmod(meeting_end, 60)
    day_str = "Monday" if meeting_day == 0 else "Tuesday"
    print(f"A valid meeting time is on {day_str} from {start_hour:02d}:{start_min:02d} to {end_hour:02d}:{end_min:02d}.")
else:
    print("No valid meeting time could be found that meets all constraints.")