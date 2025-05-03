from z3 import Solver, Int, Or, sat

# Meeting parameters:
duration = 30  # meeting duration in minutes
start = Int("start")  # meeting start time (in minutes from midnight)

# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
WORK_START = 540
WORK_END = 1020

# Busy schedules (times in minutes from midnight)

# Ethan's busy schedule:
# Monday:
#   15:30 to 16:00 -> (930, 960)
#   16:30 to 17:00 -> (990, 1020)
# Tuesday:
#   12:00 to 12:30 -> (720, 750)
#   13:00 to 13:30 -> (780, 810)
#   14:00 to 14:30 -> (840, 870)
#   15:30 to 16:00 -> (930, 960)
ethan_busy = {
    0: [(930, 960), (990, 1020)],
    1: [(720, 750), (780, 810), (840, 870), (930, 960)]
}

# Julia's busy schedule:
# Monday:
#   9:00 to 11:00   -> (540, 660)
#   11:30 to 14:30  -> (690, 870)
#   15:00 to 15:30  -> (900, 930)
#   16:00 to 17:00  -> (960, 1020)
# Tuesday:
#   9:00 to 10:00   -> (540, 600)
#   10:30 to 12:30  -> (630, 750)
#   13:00 to 13:30  -> (780, 810)
#   14:00 to 17:00  -> (840, 1020)
julia_busy = {
    0: [(540, 660), (690, 870), (900, 930), (960, 1020)],
    1: [(540, 600), (630, 750), (780, 810), (840, 1020)]
}

# Additional Constraint:
# Ethan does not want to meet on Monday before 13:00 (i.e., before 13:00 which is 780 minutes)
# No extra restriction for Tuesday.

# Helper function: ensures meeting interval [start, start+duration) does not overlap with a busy interval [busy_start, busy_end)
def non_overlap(busy_start, busy_end):
    return Or(start + duration <= busy_start, start >= busy_end)

found = False
meeting_day = None  # 0: Monday, 1: Tuesday
meeting_start = None

# We'll try scheduling on Monday (day 0) and then Tuesday (day 1)
for day in [0, 1]:
    solver = Solver()
    # The meeting must be within the work hours
    solver.add(start >= WORK_START, start + duration <= WORK_END)
    
    # Day-specific constraints:
    if day == 0:
        # Ethan does not want to meet on Monday before 13:00 (780 minutes)
        solver.add(start >= 780)
    # (No additional time constraint for Tuesday)
    
    # Add Ethan's busy intervals for the day
    for b_start, b_end in ethan_busy.get(day, []):
        solver.add(non_overlap(b_start, b_end))
    
    # Add Julia's busy intervals for the day
    for b_start, b_end in julia_busy.get(day, []):
        solver.add(non_overlap(b_start, b_end))
    
    # Try possible start times (minute granularity) within the work day
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
    # Convert minutes to HH:MM format for readability
    start_hour, start_min = divmod(meeting_start, 60)
    end_hour, end_min = divmod(meeting_end, 60)
    day_str = "Monday" if meeting_day == 0 else "Tuesday"
    print(f"A valid meeting time is on {day_str} from {start_hour:02d}:{start_min:02d} to {end_hour:02d}:{end_min:02d}.")
else:
    print("No valid meeting time could be found that meets all constraints.")