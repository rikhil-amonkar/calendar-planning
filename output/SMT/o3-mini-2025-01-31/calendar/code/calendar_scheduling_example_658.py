from z3 import Solver, Int, Or, sat

# Meeting parameters
duration = 30  # meeting duration in minutes (0.5 hour)
start = Int("start")  # meeting start time in minutes from midnight

# Work hours: from 9:00 (540 minutes) to 17:00 (1020 minutes)
WORK_START = 540
WORK_END = 1020

# Busy schedules (all times in minutes from midnight):

# Shirley's busy schedule:
# Monday:
#   10:30 to 11:00 -> (630, 660)
#   12:00 to 12:30 -> (720, 750)
#   16:00 to 16:30 -> (960, 990)
# Tuesday:
#   9:30 to 10:00  -> (570, 600)
shirley_busy = {
    0: [(630, 660), (720, 750), (960, 990)],
    1: [(570, 600)]
}

# Albert's busy schedule:
# Monday:
#   9:00 to 17:00 -> (540, 1020)
# Tuesday:
#   9:30 to 11:00  -> (570, 660)
#   11:30 to 12:30 -> (690, 750)
#   13:00 to 16:00 -> (780, 960)
#   16:30 to 17:00 -> (990, 1020)
albert_busy = {
    0: [(540, 1020)],
    1: [(570, 660), (690, 750), (780, 960), (990, 1020)]
}

# Additional constraint:
# Shirley would rather not meet on Tuesday after 10:30.
# Thus, when scheduling on Tuesday (day 1), the meeting must start before 10:30 (i.e., before 10*60+30 = 630 minutes).

# Helper function to ensure the meeting [start, start+duration) does not overlap a busy interval [busy_start, busy_end)
def non_overlap(busy_start, busy_end):
    return Or(start + duration <= busy_start, start >= busy_end)

found = False
meeting_day = None  # 0 for Monday, 1 for Tuesday
meeting_start = None

# We'll try scheduling day by day.
# Although either day is allowed, Monday seems unlikely because Albert is busy all day.
# So, we first try Tuesday (day 1) then Monday.
for day in [1, 0]:
    solver = Solver()
    
    # Meeting must be within working hours.
    solver.add(start >= WORK_START, start + duration <= WORK_END)
    
    # If scheduling on Tuesday, add Shirley's preference.
    if day == 1:
        solver.add(start < 630)  # Must start before 10:30 on Tuesday.
    
    # Add busy constraints for Shirley.
    for (busy_start, busy_end) in shirley_busy.get(day, []):
        solver.add(non_overlap(busy_start, busy_end))
        
    # Add busy constraints for Albert.
    for (busy_start, busy_end) in albert_busy.get(day, []):
        solver.add(non_overlap(busy_start, busy_end))
    
    # Check possible start times by iterating minute-by-minute.
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
    start_hour, start_min = divmod(meeting_start, 60)
    end_hour, end_min = divmod(meeting_end, 60)
    day_str = "Monday" if meeting_day == 0 else "Tuesday"
    print(f"A valid meeting time is on {day_str} from {start_hour:02d}:{start_min:02d} to {end_hour:02d}:{end_min:02d}.")
else:
    print("No valid meeting time could be found that meets all constraints.")