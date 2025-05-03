from z3 import Solver, Int, Or, sat

# Meeting parameters:
duration = 60  # meeting duration in minutes (1 hour)
start = Int("start")  # meeting start time in minutes from midnight

# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
WORK_START = 540
WORK_END = 1020

# Busy schedules (times in minutes from midnight):

# Mason has no meetings, so we don't need to block any time for him.

# Gary's schedule:
# Monday: 9:00 to 14:30 -> (540, 870), 16:00 to 17:00 -> (960, 1020)
# Tuesday: 9:00 to 11:00  -> (540, 660), 11:30 to 14:00 -> (690, 840),
#          15:30 to 16:00 -> (930, 960), 16:30 to 17:00 -> (990, 1020)
gary_busy = {
    0: [(540, 870), (960, 1020)],  # Monday (day = 0)
    1: [(540, 660), (690, 840), (930, 960), (990, 1020)]  # Tuesday (day = 1)
}

# Helper function: the meeting interval [start, start+duration) must not overlap
# with a busy interval [busy_start, busy_end)
def non_overlap(busy_start, busy_end):
    return Or(start + duration <= busy_start, start >= busy_end)

# We want the earliest availability overall, trying Monday first then Tuesday.
found = False
meeting_day = None  # 0 for Monday, 1 for Tuesday
meeting_start = None

for day_val in [0, 1]:
    solver = Solver()
    # Add common work hour constraint.
    solver.add(start >= WORK_START, start + duration <= WORK_END)
    
    # Add Gary's busy constraints for the given day.
    for interval in gary_busy[day_val]:
        busy_start, busy_end = interval
        solver.add(non_overlap(busy_start, busy_end))
    
    # Iterate minute-by-minute over possible start times and pick the earliest valid meeting.
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