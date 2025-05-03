from z3 import Solver, Int, Or, sat

# Meeting parameters:
duration = 60  # meeting duration in minutes (1 hour)
start = Int("start")  # meeting start time in minutes from midnight

# Work hours: from 9:00 (540 minutes) to 17:00 (1020 minutes)
WORK_START = 540
WORK_END = 1020

# Busy schedules (times are in minutes from midnight):

# Gary's busy schedule:
# Monday:
#   9:30 to 10:00 -> (570, 600)
#   11:00 to 13:00 -> (660, 780)
#   14:00 to 14:30 -> (840, 870)
#   16:30 to 17:00 -> (990, 1020)
# Tuesday:
#   9:00 to 9:30  -> (540, 570)
#   10:30 to 11:00 -> (630, 660)
#   14:30 to 16:00 -> (870, 960)
gary_busy = {
    0: [(570, 600), (660, 780), (840, 870), (990, 1020)],
    1: [(540, 570), (630, 660), (870, 960)]
}

# David's busy schedule:
# Monday:
#   9:00 to 9:30  -> (540, 570)
#   10:00 to 13:00 -> (600, 780)
#   14:30 to 16:30 -> (870, 990)
# Tuesday:
#   9:00 to 9:30   -> (540, 570)
#   10:00 to 10:30 -> (600, 630)
#   11:00 to 12:30 -> (660, 750)
#   13:00 to 14:30 -> (780, 870)
#   15:00 to 16:00 -> (900, 960)
#   16:30 to 17:00 -> (990, 1020)
david_busy = {
    0: [(540, 570), (600, 780), (870, 990)],
    1: [(540, 570), (600, 630), (660, 750), (780, 870), (900, 960), (990, 1020)]
}

# Helper function:
# Ensures that the meeting interval [start, start+duration) does not overlap with a busy interval [busy_start, busy_end)
def non_overlap(busy_start, busy_end):
    return Or(start + duration <= busy_start, start >= busy_end)

found = False
meeting_day = None  # 0 for Monday, 1 for Tuesday
meeting_start = None

# Try scheduling by day.
for day in [0, 1]:
    solver = Solver()
    # Meeting must be within working hours.
    solver.add(start >= WORK_START, start + duration <= WORK_END)
    
    # Add busy constraints for Gary.
    for (busy_start, busy_end) in gary_busy.get(day, []):
        solver.add(non_overlap(busy_start, busy_end))
    
    # Add busy constraints for David.
    for (busy_start, busy_end) in david_busy.get(day, []):
        solver.add(non_overlap(busy_start, busy_end))
    
    # Iterate over possible starting times (minute by minute) within working hours.
    for t in range(WORK_START, WORK_END - duration + 1):
        solver.push()
        solver.add(start == t)
        if solver.check() == sat:
            meeting_start = t
            meeting_day = day
            found = True
            solver.pop()  # Pop the equality constraint
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