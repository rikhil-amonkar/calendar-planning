from z3 import Solver, Int, Or, sat

# Meeting parameters:
duration = 60  # meeting duration in minutes (1 hour)
start = Int("start")  # meeting start time in minutes from midnight

# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
WORK_START = 540
WORK_END = 1020

# Busy schedules (times in minutes from midnight):

# Kyle's busy schedule:
# Tuesday: 11:00-11:30 -> (660, 690), 14:00-14:30 -> (840, 870)
# (Kyle is available on Monday for the entire day.)
kyle_busy = {
    1: [(660, 690), (840, 870)]
}

# Sharon's busy schedule:
# Monday: Busy the entire day: 9:00-17:00 -> (540, 1020)
# Tuesday: 9:00-10:00 -> (540, 600), 11:00-12:00 -> (660, 720), 
#          12:30-13:30 -> (750, 810), 14:00-17:00 -> (840, 1020)
sharon_busy = {
    0: [(540, 1020)],
    1: [(540, 600), (660, 720), (750, 810), (840, 1020)]
}

# Helper function to ensure that meeting time [start, start+duration)
# does not overlap with a busy interval [busy_start, busy_end)
def non_overlap(busy_start, busy_end):
    return Or(start + duration <= busy_start, start >= busy_end)

found = False
meeting_day = None  # 0 for Monday, 1 for Tuesday
meeting_start = None

# We check each day (Monday then Tuesday) for a valid meeting slot.
for day_val in [0, 1]:
    solver = Solver()
    # Constraint: meeting must lie within work hours.
    solver.add(start >= WORK_START, start + duration <= WORK_END)
    
    # Add Kyle's busy constraints for the day.
    for interval in kyle_busy.get(day_val, []):
        busy_start, busy_end = interval
        solver.add(non_overlap(busy_start, busy_end))
        
    # Add Sharon's busy constraints for the day.
    for interval in sharon_busy.get(day_val, []):
        busy_start, busy_end = interval
        solver.add(non_overlap(busy_start, busy_end))
    
    # Iterate minute-by-minute in the work day to find the earliest valid meeting
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
    day_name = "Monday" if meeting_day == 0 else "Tuesday"
    print(f"A valid meeting time is on {day_name} from {s_hour:02d}:{s_min:02d} to {e_hour:02d}:{e_min:02d}.")
else:
    print("No valid meeting time could be found.")