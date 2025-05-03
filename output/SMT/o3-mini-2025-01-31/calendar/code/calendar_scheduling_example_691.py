from z3 import Solver, Int, Or, sat

# Meeting parameters:
duration = 30  # meeting duration in minutes (half an hour)
start = Int("start")  # meeting start time in minutes from midnight

# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
WORK_START = 540
WORK_END = 1020

# Busy schedules (times in minutes)
# Joe's busy schedule:
# Monday:
#   9:30 to 10:30  -> (570, 630)
#   11:00 to 12:30 -> (660, 750)
#   13:30 to 14:00 -> (810, 840)
# Tuesday:
#   14:00 to 14:30 -> (840, 870)
#   16:00 to 16:30 -> (960, 990)
joe_busy = {
    0: [(570, 630), (660, 750), (810, 840)],
    1: [(840, 870), (960, 990)]
}

# Walter's busy schedule:
# Monday:
#   9:00 to 9:30   -> (540, 570)
#   10:00 to 12:30 -> (600, 750)
#   14:00 to 15:30 -> (840, 930)
#   16:00 to 17:00 -> (960, 1020)
# Tuesday:
#   9:30 to 10:00  -> (570, 600)
#   10:30 to 14:00 -> (630, 840)
#   14:30 to 17:00 -> (870, 1020)
walter_busy = {
    0: [(540, 570), (600, 750), (840, 930), (960, 1020)],
    1: [(570, 600), (630, 840), (870, 1020)]
}

# Helper function to ensure the meeting [start, start+duration)
# does not overlap with a busy interval [busy_start, busy_end).
def non_overlap(busy_start, busy_end):
    return Or(start + duration <= busy_start, start >= busy_end)

# We have two extra constraints:
# 1. Joe does not want to meet on Monday after 15:30, so if the meeting is on Monday (day 0),
#    then the meeting must finish by 15:30 (15:30 = 930 minutes), i.e., start + duration <= 930.
# 2. Walter prefers to avoid more meetings on Tuesday, so we will try scheduling on Monday first.
found = False
meeting_day = None  # 0 for Monday, 1 for Tuesday
meeting_start = None

# Try Monday first (day 0) then Tuesday (day 1)
for day in [0, 1]:
    solver = Solver()
    # Meeting must be within work hours
    solver.add(start >= WORK_START, start + duration <= WORK_END)
    
    # Apply Joe and Walter busy constraints.
    for b_start, b_end in joe_busy.get(day, []):
        solver.add(non_overlap(b_start, b_end))
    for b_start, b_end in walter_busy.get(day, []):
        solver.add(non_overlap(b_start, b_end))
        
    # Extra constraint for Monday: Joe does not want meetings after 15:30.
    if day == 0:
        solver.add(start + duration <= 930)  # meeting must finish by 15:30
    
    # For each candidate time (earlier times first), try to find a valid meeting time.
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
    start_hour, start_min = divmod(meeting_start, 60)
    end_hour, end_min = divmod(meeting_end, 60)
    day_str = "Monday" if meeting_day == 0 else "Tuesday"
    print(f"A valid meeting time is on {day_str} from {start_hour:02d}:{start_min:02d} to {end_hour:02d}:{end_min:02d}.")
else:
    print("No valid meeting time could be found that meets all constraints.")