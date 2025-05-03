from z3 import Solver, Int, Or, sat

# Meeting parameters:
duration = 30  # meeting duration in minutes (half an hour)
start = Int("start")  # meeting start time (in minutes from midnight)

# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
WORK_START = 540
WORK_END = 1020

# Busy schedules (times in minutes from midnight):

# Paul’s schedule:
# Monday: 10:30 to 11:00 -> (630, 660), 12:00 to 13:00 -> (720, 780),
#         14:00 to 15:00 -> (840, 900), 16:00 to 17:00 -> (960, 1020)
# Tuesday: 11:30 to 12:00 -> (690, 720), 12:30 to 13:00 -> (750, 780),
#          13:30 to 14:30 -> (810, 870), 15:30 to 16:00 -> (930, 960)
paul_busy = {
    0: [(630, 660), (720, 780), (840, 900), (960, 1020)],  # Monday (day = 0)
    1: [(690, 720), (750, 780), (810, 870), (930, 960)]       # Tuesday (day = 1)
}

# Sophia’s schedule:
# Monday: Busy the entire day: 9:00 to 17:00 -> (540, 1020)
# Tuesday: 9:00 to 9:30 -> (540, 570), 10:00 to 14:00 -> (600, 840),
#          14:30 to 17:00 -> (870, 1020)
sophia_busy = {
    0: [(540, 1020)],  # Monday
    1: [(540, 570), (600, 840), (870, 1020)]  # Tuesday
}

# Helper function: Ensures that the meeting interval [start, start+duration)
# does not overlap with a busy interval [busy_start, busy_end)
def non_overlap(busy_start, busy_end):
    return Or(start + duration <= busy_start, start >= busy_end)

found = False
meeting_day = None  # 0 for Monday, 1 for Tuesday
meeting_start = None

# We check each day (Monday = 0, Tuesday = 1) for a valid meeting slot.
for day_val in [0, 1]:
    solver = Solver()
    # Meeting must be within work hours.
    solver.add(start >= WORK_START, start + duration <= WORK_END)
    
    # Paul’s busy constraints for the day
    for interval in paul_busy.get(day_val, []):
        busy_start, busy_end = interval
        solver.add(non_overlap(busy_start, busy_end))
    
    # Sophia’s busy constraints for the day.
    for interval in sophia_busy.get(day_val, []):
        busy_start, busy_end = interval
        solver.add(non_overlap(busy_start, busy_end))
    
    # Search for the earliest start time (minute-by-minute)
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