from z3 import Solver, Int, Or, sat

# Meeting parameters:
duration = 60  # meeting duration in minutes (1 hour)
start = Int("start")  # meeting start time in minutes from midnight

# Work hours: from 9:00 (540 minutes) to 17:00 (1020 minutes)
WORK_START = 540
WORK_END = 1020

# Busy schedules (times expressed in minutes from midnight):

# Emily's busy schedule:
# Monday:
#   10:00 to 10:30 -> (600, 630)
#   12:30 to 14:30 -> (750, 870)
# Tuesday:
#   14:00 to 15:00 -> (840, 900)
#   15:30 to 16:00 -> (930, 960)
emily_busy = {
    0: [(600, 630), (750, 870)],
    1: [(840, 900), (930, 960)]
}

# Lawrence's busy schedule:
# Monday:
#   9:00 to 17:00 -> (540, 1020)  --> Fully busy
# Tuesday:
#   9:00 to 10:00  -> (540, 600)
#   11:00 to 12:00 -> (660, 720)
#   12:30 to 13:30 -> (750, 810)
#   14:00 to 17:00 -> (840, 1020)
lawrence_busy = {
    0: [(540, 1020)],
    1: [(540, 600), (660, 720), (750, 810), (840, 1020)]
}

# Helper function to ensure that the meeting interval [start, start + duration)
# does not overlap with a given busy interval [busy_start, busy_end).
def non_overlap(busy_start, busy_end):
    return Or(start + duration <= busy_start, start >= busy_end)

found = False
meeting_day = None  # 0 for Monday, 1 for Tuesday
meeting_start = None

# Try scheduling on Monday (day 0) and Tuesday (day 1)
for day in [0, 1]:
    solver = Solver()
    
    # The meeting must fit within work hours.
    solver.add(start >= WORK_START, start + duration <= WORK_END)
    
    # Add Emily's busy intervals constraints for the day.
    for interval in emily_busy.get(day, []):
        solver.add(non_overlap(interval[0], interval[1]))
    
    # Add Lawrence's busy intervals constraints for the day.
    for interval in lawrence_busy.get(day, []):
        solver.add(non_overlap(interval[0], interval[1]))
    
    # Try every possible start time (minute granularity) within work hours.
    for t in range(WORK_START, WORK_END - duration + 1):
        solver.push()
        solver.add(start == t)
        if solver.check() == sat:
            meeting_start = t
            meeting_day = day
            found = True
            solver.pop()  # Remove the temporary constraint.
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