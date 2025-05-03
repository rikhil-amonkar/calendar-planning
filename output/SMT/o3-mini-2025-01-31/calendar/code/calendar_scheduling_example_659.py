from z3 import Solver, Int, Or, sat

# Meeting parameters:
duration = 60  # meeting duration in minutes (1 hour)
start = Int("start")  # meeting start time in minutes from midnight

# Work hours: from 9:00 (540) to 17:00 (1020)
WORK_START = 540
WORK_END = 1020

# Busy schedules (all times represented in minutes from midnight):

# Barbara's busy schedule:
# Monday:
#   12:30 to 13:00 -> (750, 780)
#   13:30 to 14:00 -> (810, 840)
#   14:30 to 16:00 -> (870, 960)
# Tuesday:
#   10:00 to 10:30 -> (600, 630)
#   15:30 to 16:00 -> (930, 960)
#   16:30 to 17:00 -> (990, 1020)
barbara_busy = {
    0: [(750, 780), (810, 840), (870, 960)],
    1: [(600, 630), (930, 960), (990, 1020)]
}

# Jose's busy schedule:
# Monday:
#   9:00 to 10:00   -> (540, 600)
#   11:00 to 12:00  -> (660, 720)
#   12:30 to 13:30  -> (750, 810)
#   14:30 to 15:00  -> (870, 900)
#   15:30 to 16:00  -> (930, 960)
#   16:30 to 17:00  -> (990, 1020)
# Tuesday:
#   9:30 to 12:00   -> (570, 720)
#   13:00 to 17:00  -> (780, 1020)
jose_busy = {
    0: [(540, 600), (660, 720), (750, 810), (870, 900), (930, 960), (990, 1020)],
    1: [(570, 720), (780, 1020)]
}

# Additional constraint:
# Jose cannot meet on Monday.
# That means if we try to schedule on Monday (day 0), the constraints should make it unsolvable.
# We can enforce that by adding a constraint that is always false for day 0.

# Helper function to ensure that the meeting interval [start, start+duration)
# does not overlap with a busy interval [busy_start, busy_end)
def non_overlap(busy_start, busy_end):
    # Either the meeting ends before the busy interval starts,
    # or the meeting starts after the busy interval ends.
    return Or(start + duration <= busy_start, start >= busy_end)

found = False
meeting_day = None  # 0 for Monday, 1 for Tuesday
meeting_start = None

# We try scheduling for Tuesday first because Jose cannot meet on Monday.
for day in [1, 0]:
    solver = Solver()
    
    # Meeting must be within the work hours.
    solver.add(start >= WORK_START, start + duration <= WORK_END)
    
    # Enforce Jose's constraint: he cannot have a meeting on Monday.
    if day == 0:
        solver.add(False)  # Force Monday to be unsolvable.
    
    # Add Barbara's busy constraints for the given day.
    for (busy_start, busy_end) in barbara_busy.get(day, []):
        solver.add(non_overlap(busy_start, busy_end))
        
    # Add Jose's busy constraints for the given day.
    for (busy_start, busy_end) in jose_busy.get(day, []):
        solver.add(non_overlap(busy_start, busy_end))
    
    # Check all possible start times (minute-by-minute) that fit in the working hours.
    for t in range(WORK_START, WORK_END - duration + 1):
        solver.push()
        solver.add(start == t)
        if solver.check() == sat:
            meeting_start = t
            meeting_day = day
            found = True
            solver.pop()  # remove the equality constraint after a solution is found.
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