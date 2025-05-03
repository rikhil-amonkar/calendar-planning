from z3 import Solver, Int, Or, sat

# Meeting parameters:
duration = 30  # meeting duration in minutes
start = Int("start")  # meeting start time, represented in minutes from midnight

# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
WORK_START = 540
WORK_END = 1020

# Busy schedules (times in minutes from midnight)

# Jerry's busy schedule:
# On Tuesday only:
#   9:00 to 9:30 -> (540, 570)
#   10:00 to 10:30 -> (600, 630)
#   12:00 to 12:30 -> (720, 750)
#   16:00 to 16:30 -> (960, 990)
jerry_busy = {
    # Monday: no blocks mentioned, so available all day.
    0: [],
    # Tuesday:
    1: [(540, 570), (600, 630), (720, 750), (960, 990)]
}

# Edward's busy schedule:
# Monday:
#   9:30 to 10:00 -> (570, 600)
#   10:30 to 12:00 -> (630, 720)
#   12:30 to 14:00 -> (750, 840)
#   14:30 to 17:00 -> (870, 1020)
# Tuesday:
#   9:00 to 17:00 -> (540, 1020)
edward_busy = {
    0: [(570, 600), (630, 720), (750, 840), (870, 1020)],
    1: [(540, 1020)]
}

# The group would like to meet at their earliest availability.
# This means we should consider the days in order and check for the earliest possible meeting time.

# Helper function to ensure that the meeting interval [start, start+duration)
# does not overlap with a given busy interval [busy_start, busy_end)
def non_overlap(busy_start, busy_end):
    return Or(start + duration <= busy_start, start >= busy_end)

found = False
meeting_day = None  # 0 for Monday, 1 for Tuesday
meeting_start = None

# We try Monday (day 0) first, then Tuesday (day 1)
for day in [0, 1]:
    solver = Solver()
    # Constrain meeting to be within work hours.
    solver.add(start >= WORK_START, start + duration <= WORK_END)
    
    # Add Jerry's busy times for this day.
    for b_start, b_end in jerry_busy.get(day, []):
        solver.add(non_overlap(b_start, b_end))
    
    # Add Edward's busy times for this day.
    for b_start, b_end in edward_busy.get(day, []):
        solver.add(non_overlap(b_start, b_end))
    
    # Iterate through the possible start times in increasing order (earlier times first).
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
    # Convert minutes to HH:MM format for easier reading.
    start_hour, start_min = divmod(meeting_start, 60)
    end_hour, end_min = divmod(meeting_end, 60)
    day_str = "Monday" if meeting_day == 0 else "Tuesday"
    print(f"A valid meeting time is on {day_str} from {start_hour:02d}:{start_min:02d} to {end_hour:02d}:{end_min:02d}.")
else:
    print("No valid meeting time could be found that meets all constraints.")