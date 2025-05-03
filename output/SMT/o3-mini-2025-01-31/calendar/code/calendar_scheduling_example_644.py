from z3 import Solver, Int, Or, sat

# Meeting parameters:
duration = 60  # meeting duration in minutes (1 hour)
start = Int("start")  # meeting start time (in minutes from midnight)

# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
WORK_START = 540
WORK_END = 1020

# Busy schedules (times in minutes from midnight):

# Emily's busy schedule:
# Monday: 9:00-9:30   -> (540, 570)
#         10:00-11:00 -> (600, 660)
#         12:00-13:00 -> (720, 780)
#         13:30-14:30 -> (810, 870)
#         16:00-16:30 -> (960, 990)
# Tuesday: 9:00-9:30  -> (540, 570)
#          11:00-11:30 -> (660, 690)
#          12:00-13:00 -> (720, 780)
#          15:30-16:00 -> (930, 960)
#          16:30-17:00 -> (990, 1020)
emily_busy = {
    0: [(540, 570), (600, 660), (720, 780), (810, 870), (960, 990)],
    1: [(540, 570), (660, 690), (720, 780), (930, 960), (990, 1020)]
}

# Mark's busy schedule:
# Monday: 9:00-10:00   -> (540, 600)
#         10:30-11:00 -> (630, 660)
#         12:00-12:30 -> (720, 750)
#         13:00-16:30 -> (780, 990)
# Tuesday: 9:30-10:00  -> (570, 600)
#          10:30-11:30 -> (630, 690)
#          12:00-13:30 -> (720, 810)
#          14:00-16:00 -> (840, 960)
#          16:30-17:00 -> (990, 1020)
mark_busy = {
    0: [(540, 600), (630, 660), (720, 750), (780, 990)],
    1: [(570, 600), (630, 690), (720, 810), (840, 960), (990, 1020)]
}

# Helper function: meeting interval [start, start+duration)
# must not overlap with a busy interval [busy_start, busy_end)
def non_overlap(busy_start, busy_end):
    return Or(start + duration <= busy_start, start >= busy_end)

found = False
meeting_day = None  # 0 for Monday, 1 for Tuesday
meeting_start = None

# We try each day (Monday then Tuesday) to find the earliest valid meeting time.
for day_val in [0, 1]:
    solver = Solver()
    
    # Constraint: meeting must lie within work hours.
    solver.add(start >= WORK_START, start + duration <= WORK_END)
    
    # Add Emily's busy constraints for the day.
    for interval in emily_busy.get(day_val, []):
        busy_start, busy_end = interval
        solver.add(non_overlap(busy_start, busy_end))
    
    # Add Mark's busy constraints for the day.
    for interval in mark_busy.get(day_val, []):
        busy_start, busy_end = interval
        solver.add(non_overlap(busy_start, busy_end))
    
    # Search for the earliest valid start time (minute-by-minute)
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
    s_hour, s_min = divmod(meeting_start, 60)
    e_hour, e_min = divmod(meeting_end, 60)
    day_str = "Monday" if meeting_day == 0 else "Tuesday"
    print(f"A valid meeting time is on {day_str} from {s_hour:02d}:{s_min:02d} to {e_hour:02d}:{e_min:02d}.")
else:
    print("No valid meeting time could be found.")