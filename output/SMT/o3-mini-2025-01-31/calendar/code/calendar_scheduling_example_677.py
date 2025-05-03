from z3 import Solver, Int, Or, sat

# Meeting parameters:
duration = 60  # meeting duration in minutes (1 hour)
start = Int("start")  # meeting start time, in minutes from midnight

# Work hours: 9:00 (540) to 17:00 (1020)
WORK_START = 540
WORK_END = 1020

# Busy schedules (times in minutes from midnight)

# Lisa's busy schedule:
# Monday:
#   11:00 to 11:30 -> (660, 690)
#   13:30 to 14:00 -> (810, 840)
#   15:00 to 15:30 -> (900, 930)
#   16:00 to 16:30 -> (960, 990)
# Tuesday:
#   10:30 to 11:00 -> (630, 660)
#   15:00 to 15:30 -> (900, 930)
lisa_busy = {
    0: [(660, 690), (810, 840), (900, 930), (960, 990)],
    1: [(630, 660), (900, 930)]
}

# Lauren's busy schedule:
# Monday:
#   9:30 to 10:00   -> (570, 600)
#   10:30 to 13:30  -> (630, 810)
#   15:00 to 16:30  -> (900, 990)
# Tuesday:
#   9:30 to 10:00   -> (570, 600)
#   10:30 to 11:30  -> (630, 690)
#   13:30 to 14:30  -> (810, 870)
#   16:30 to 17:00  -> (990, 1020)
lauren_busy = {
    0: [(570, 600), (630, 810), (900, 990)],
    1: [(570, 600), (630, 690), (810, 870), (990, 1020)]
}

# Additional constraints:
# - Lisa does NOT want to meet on Tuesday after 15:30.
#   Since the meeting lasts one hour, on Tuesday the meeting must finish by 15:30,
#   i.e. start + duration <= 15:30 (930 minutes).
#
# - Lauren cannot meet on Monday.
#   So meetings on Monday are not allowed.

# Helper function: meeting interval [start, start+duration) must not overlap with busy interval [busy_start, busy_end)
def non_overlap(busy_start, busy_end):
    return Or(start + duration <= busy_start, start >= busy_end)

found = False
meeting_day = None   # 0 for Monday, 1 for Tuesday
meeting_start = None

# Try both days: Monday (day 0) and Tuesday (day 1)
for day in [0, 1]:
    solver = Solver()
    # Meeting must be scheduled within work hours.
    solver.add(start >= WORK_START, start + duration <= WORK_END)
    
    # Add additional day-specific constraints.
    if day == 0:
        # Lauren cannot meet on Monday.
        solver.add(False)
    elif day == 1:
        # Lisa does not want to meet on Tuesday after 15:30.
        # So on Tuesday the meeting must end by 15:30 (930 minutes).
        solver.add(start + duration <= 930)
    
    # Add Lisa's busy intervals constraints.
    for b_start, b_end in lisa_busy.get(day, []):
        solver.add(non_overlap(b_start, b_end))
    
    # Add Lauren's busy intervals constraints.
    for b_start, b_end in lauren_busy.get(day, []):
        solver.add(non_overlap(b_start, b_end))
    
    # Try possible start times (minute granularity) within work hours.
    for t in range(WORK_START, WORK_END - duration + 1):
        solver.push()
        solver.add(start == t)
        if solver.check() == sat:
            meeting_start = t
            meeting_day = day
            found = True
            solver.pop()  # remove the temporary constraint
            break
        solver.pop()
    
    if found:
        break

if found:
    meeting_end = meeting_start + duration
    # Convert minutes into HH:MM format.
    start_hr, start_min = divmod(meeting_start, 60)
    end_hr, end_min = divmod(meeting_end, 60)
    day_str = "Monday" if meeting_day == 0 else "Tuesday"
    print(f"A valid meeting time is on {day_str} from {start_hr:02d}:{start_min:02d} to {end_hr:02d}:{end_min:02d}.")
else:
    print("No valid meeting time could be found that meets all constraints.")