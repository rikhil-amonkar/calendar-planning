from z3 import Solver, Int, Or, sat

# Meeting parameters:
duration = 30  # meeting duration in minutes (half an hour)
start = Int("start")  # meeting start time in minutes from midnight

# Work hours: from 9:00 (540 minutes) to 17:00 (1020 minutes)
WORK_START = 540
WORK_END = 1020

# Busy schedules (times expressed in minutes from midnight):

# Jean's busy schedule:
# Monday: (none)
# Tuesday:
#   11:30 to 12:00 -> (690, 720)
#   16:00 to 16:30 -> (960, 990)
jean_busy = {
    0: [],
    1: [(690, 720), (960, 990)]
}

# Doris's busy schedule:
# Monday:
#   9:00 to 11:30   -> (540, 690)
#   12:00 to 12:30  -> (720, 750)
#   13:30 to 16:00  -> (810, 960)
#   16:30 to 17:00  -> (990, 1020)
# Tuesday:
#   9:00 to 17:00   -> (540, 1020)
doris_busy = {
    0: [(540, 690), (720, 750), (810, 960), (990, 1020)],
    1: [(540, 1020)]
}

# Additional preference:
# Doris would rather not meet on Monday after 14:00.
# For Monday (day 0), we require that the meeting ends by 14:00 (840 minutes): start + duration <= 840

# Helper function to ensure that the meeting interval [start, start+duration) does NOT overlap 
# with a busy interval [busy_start, busy_end)
def non_overlap(busy_start, busy_end):
    return Or(start + duration <= busy_start, start >= busy_end)

found = False
meeting_day = None  # 0 for Monday, 1 for Tuesday
meeting_start = None

# Check Monday first (day = 0), then Tuesday (day = 1)
for day in [0, 1]:
    solver = Solver()
    # Ensure meeting fits within the work hours.
    solver.add(start >= WORK_START, start + duration <= WORK_END)
    
    # For Monday, add Doris's timing preference: meeting must end by 14:00 (840 minutes)
    if day == 0:
        solver.add(start + duration <= 840)
    
    # Add Jean's busy intervals for the day.
    for b_start, b_end in jean_busy.get(day, []):
        solver.add(non_overlap(b_start, b_end))
    
    # Add Doris's busy intervals for the day.
    for b_start, b_end in doris_busy.get(day, []):
        solver.add(non_overlap(b_start, b_end))
    
    # Search for a valid start time minute-by-minute.
    for t in range(WORK_START, WORK_END - duration + 1):
        solver.push()
        solver.add(start == t)
        if solver.check() == sat:
            meeting_start = t
            meeting_day = day
            found = True
            solver.pop()  # remove the temporary constraint before breaking out
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