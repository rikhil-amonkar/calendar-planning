from z3 import Solver, Int, Or, sat

# Meeting parameters:
duration = 60  # meeting duration in minutes (1 hour)
start = Int("start")  # meeting start time in minutes from midnight

# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
WORK_START = 540
WORK_END = 1020

# Busy schedules (times in minutes from midnight):

# Christopher's schedule:
# Monday: 9:00 to 9:30 -> (540, 570), 10:30 to 11:00 -> (630, 660), 14:00 to 14:30 -> (840, 870)
# Tuesday: 13:30 to 14:00 -> (810, 840)
christopher_busy = {
    0: [(540, 570), (630, 660), (840, 870)],   # Monday (day = 0)
    1: [(810, 840)]                             # Tuesday (day = 1)
}

# Jean's schedule:
# Monday: 9:00 to 10:00 -> (540, 600), 10:30 to 11:00 -> (630, 660), 
#         11:30 to 12:30 -> (690, 750), 13:30 to 15:00 -> (810, 900),
#         15:30 to 16:00 -> (930, 960)
# Tuesday: 9:00 to 10:00 -> (540, 600), 10:30 to 12:00 -> (630, 720),
#          13:00 to 17:00 -> (780, 1020)
jean_busy = {
    0: [(540, 600), (630, 660), (690, 750), (810, 900), (930, 960)],  # Monday (day = 0)
    1: [(540, 600), (630, 720), (780, 1020)]                             # Tuesday (day = 1)
}

# Helper function: the meeting interval [start, start+duration) must not overlap
# with a busy interval [busy_start, busy_end)
def non_overlap(busy_start, busy_end):
    return Or(start + duration <= busy_start, start >= busy_end)

# Christopher prefers not to meet on Monday.
# Thus, we try Tuesday (day 1) first, and use Monday only if Tuesday doesn't yield a solution.
found = False
meeting_day = None  # 0 for Monday, 1 for Tuesday
meeting_start = None

# Try days in preferred order: Tuesday (1) then Monday (0)
for day_val in [1, 0]:
    solver = Solver()
    # Meeting must be within work hours.
    solver.add(start >= WORK_START, start + duration <= WORK_END)
    
    # Add Christopher's busy constraints for the day.
    for interval in christopher_busy.get(day_val, []):
        busy_start, busy_end = interval
        solver.add(non_overlap(busy_start, busy_end))
    
    # Add Jean's busy constraints for the day.
    for interval in jean_busy.get(day_val, []):
        busy_start, busy_end = interval
        solver.add(non_overlap(busy_start, busy_end))
    
    # Iterate minute-by-minute over possible start times to pick the earliest valid meeting time.
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
    day_name = "Monday" if meeting_day == 0 else "Tuesday"
    print(f"A valid meeting time is on {day_name} from {start_hour:02d}:{start_min:02d} to {end_hour:02d}:{end_min:02d}.")
else:
    print("No valid meeting time could be found.")