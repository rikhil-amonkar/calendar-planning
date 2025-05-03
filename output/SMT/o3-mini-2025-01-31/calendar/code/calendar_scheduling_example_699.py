from z3 import Solver, Int, Or, sat

# Meeting parameters:
duration = 30  # meeting duration in minutes (half an hour)
start = Int("start")  # meeting start time in minutes from midnight

# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
WORK_START = 540
WORK_END = 1020

# Busy schedules for each participant on Monday (day 0) and Tuesday (day 1)

# Anna's busy schedule in minutes:
# Monday:
#   15:00 to 15:30 -> (900,930)
# Tuesday:
#   11:30 to 12:00 -> (690,720)
anna_busy = {
    0: [(900,930)],
    1: [(690,720)]
}

# Mary’s busy schedule in minutes:
# Monday:
#   9:30 to 12:00   -> (570,720)
#   13:00 to 14:30  -> (780,870)
#   15:30 to 16:00  -> (930,960)
#   16:30 to 17:00  -> (990,1020)
# Tuesday:
#   9:00 to 11:30   -> (540,690)
#   12:00 to 13:00  -> (720,780)
#   13:30 to 14:00  -> (810,840)
#   14:30 to 15:30  -> (870,930)
#   16:00 to 17:00  -> (960,1020)
mary_busy = {
    0: [(570,720), (780,870), (930,960), (990,1020)],
    1: [(540,690), (720,780), (810,840), (870,930), (960,1020)]
}

# Additional constraints:
# 1. Anna cannot meet on Monday. (So we must not schedule on day 0)
# 2. Mary would like to avoid meetings on Tuesday before 15:30.
#    We'll treat this preference as a hard constraint for Tuesday (meeting must start at or after 15:30)
#    15:30 in minutes is 15*60 + 30 = 930.

# Helper function:
# The meeting interval [start, start+duration) must not overlap with a busy interval [busy_start, busy_end).
def non_overlap(busy_start, busy_end):
    return Or(start + duration <= busy_start, start >= busy_end)

found = False
meeting_day = None  # 0 for Monday, 1 for Tuesday
meeting_start = None

# We want to consider either Monday or Tuesday, but Anna cannot meet on Monday.
# Therefore, we try Monday first; if a valid time is found, it still must meet Anna's constraint.
# For Monday (day 0), we add a constraint that effectively makes the day invalid.
for day in [0, 1]:
    solver = Solver()
    
    # Meeting must be within work hours.
    solver.add(start >= WORK_START, start + duration <= WORK_END)
    
    # Apply participant-specific busy time constraints:
    for b_start, b_end in anna_busy.get(day, []):
        solver.add(non_overlap(b_start, b_end))
    for b_start, b_end in mary_busy.get(day, []):
        solver.add(non_overlap(b_start, b_end))
    
    # Apply additional constraints:
    if day == 0:
        # Anna cannot meet on Monday.
        solver.add(False)
    else:
        # For Tuesday, Mary would like to avoid meetings before 15:30.
        solver.add(start >= 930)
    
    # Define the range for possible start times.
    # Lower bound is the maximum of WORK_START and any preference lower bound.
    lower_bound = WORK_START
    if day == 1:
        lower_bound = max(lower_bound, 930)
    upper_bound = WORK_END - duration

    for t in range(lower_bound, upper_bound + 1):
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