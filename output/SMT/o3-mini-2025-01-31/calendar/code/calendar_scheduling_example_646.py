from z3 import Solver, Int, Or, sat

# Meeting parameters:
duration = 60  # meeting duration in minutes (1 hour)
start = Int("start")  # meeting start time in minutes from midnight

# Define work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
WORK_START = 540
WORK_END = 1020

# Busy schedules (in minutes from midnight):

# Stephen's busy schedule:
# Monday:
#   9:30-10:00 -> (570, 600)
#   11:00-11:30 -> (660, 690)
#   14:00-14:30 -> (840, 870)
#   15:00-15:30 -> (900, 930)
# Tuesday:
#   10:30-11:00 -> (630, 660)
#   12:00-12:30 -> (720, 750)
#   14:30-16:30 -> (870, 990)
stephen_busy = {
    0: [(570, 600), (660, 690), (840, 870), (900, 930)],
    1: [(630, 660), (720, 750), (870, 990)]
}

# Alexis's busy schedule:
# Monday:
#   9:00-12:00 -> (540, 720)
#   12:30-13:00 -> (750, 780)
#   14:30-17:00 -> (870, 1020)
# Tuesday:
#   9:00-15:30   -> (540, 930)
#   16:00-16:30  -> (960, 990)
alexis_busy = {
    0: [(540, 720), (750, 780), (870, 1020)],
    1: [(540, 930), (960, 990)]
}

# Helper function: The meeting interval [start, start+duration)
# must not overlap with a busy interval [busy_start, busy_end)
def non_overlap(busy_start, busy_end):
    return Or(start + duration <= busy_start, start >= busy_end)

found = False
meeting_day = None   # 0 for Monday, 1 for Tuesday
meeting_start = None

# We try each day in order: Monday (0) then Tuesday (1)
for day_val in [0, 1]:
    solver = Solver()
    # The meeting must fall within work hours:
    solver.add(start >= WORK_START, start + duration <= WORK_END)
    
    # Add Stephen's busy constraints for the day:
    for (busy_start, busy_end) in stephen_busy.get(day_val, []):
        solver.add(non_overlap(busy_start, busy_end))
    
    # Add Alexis's busy constraints for the day:
    for (busy_start, busy_end) in alexis_busy.get(day_val, []):
        solver.add(non_overlap(busy_start, busy_end))
    
    # Iterate through possible start times (minute by minute)
    for t in range(WORK_START, WORK_END - duration + 1):
        solver.push()
        solver.add(start == t)
        if solver.check() == sat:
            meeting_start = t
            meeting_day = day_val
            found = True
            solver.pop()
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
    print("No valid meeting time could be found.")