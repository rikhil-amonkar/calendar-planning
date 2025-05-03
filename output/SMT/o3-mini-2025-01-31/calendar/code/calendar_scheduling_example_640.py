from z3 import Solver, Int, Or, Implies, sat

# Meeting parameters:
duration = 30  # meeting duration in minutes
start = Int("start")  # meeting start time (in minutes from midnight)

# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
WORK_START = 540
WORK_END = 1020

# Busy schedules (times in minutes from midnight):

# Bobby's schedule:
#   Monday: 14:30 to 15:00 -> (870, 900)
#   Tuesday: 9:00 to 11:30 -> (540, 690), 
#            12:00 to 12:30 -> (720, 750), 
#            13:00 to 15:00 -> (780, 900), 
#            15:30 to 17:00 -> (930, 1020)
bobby_busy = {
    0: [(870, 900)],  # Monday (day=0)
    1: [(540, 690), (720, 750), (780, 900), (930, 1020)]  # Tuesday (day=1)
}

# Michael's schedule:
#   Monday: 9:00 to 10:00 -> (540, 600), 
#           10:30 to 13:30 -> (630, 810), 
#           14:00 to 15:00 -> (840, 900), 
#           15:30 to 17:00 -> (930, 1020)
#   Tuesday: 9:00 to 10:30 -> (540, 630), 
#            11:00 to 11:30 -> (660, 690), 
#            12:00 to 14:00 -> (720, 840), 
#            15:00 to 16:00 -> (900, 960), 
#            16:30 to 17:00 -> (990, 1020)
michael_busy = {
    0: [(540, 600), (630, 810), (840, 900), (930, 1020)],  # Monday (day=0)
    1: [(540, 630), (660, 690), (720, 840), (900, 960), (990, 1020)]  # Tuesday (day=1)
}

# Helper function: meeting interval [start, start+duration) must not overlap a busy interval [busy_start, busy_end)
def non_overlap(busy_start, busy_end):
    # Either the meeting ends before the busy interval or starts after it ends.
    return Or(start + duration <= busy_start, start >= busy_end)

# We want to schedule at the earliest availability overall.
# We'll consider Monday (day=0) first, then Tuesday (day=1) if no slot is available on Monday.
found = False
meeting_day = None  # 0 for Monday, 1 for Tuesday
meeting_start = None

# Try each day in order (Monday then Tuesday)
for day_val in [0, 1]:
    solver = Solver()
    # Common constraints: meeting must be within work hours.
    solver.add(start >= WORK_START, start + duration <= WORK_END)
    
    # Add Bobby's busy constraints for the day.
    for interval in bobby_busy[day_val]:
        busy_start, busy_end = interval
        solver.add(non_overlap(busy_start, busy_end))
    
    # Add Michael's busy constraints for the day.
    for interval in michael_busy[day_val]:
        busy_start, busy_end = interval
        solver.add(non_overlap(busy_start, busy_end))
    
    # Test every possible start time (minute-by-minute) in the work day,
    # looking for the earliest start time that satisfies the constraints for that day.
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