from z3 import Solver, Int, Or, sat

# Meeting parameters
duration = 60  # meeting duration in minutes (1 hour)
start = Int("start")  # meeting start time in minutes from midnight

# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
WORK_START = 540
WORK_END = 1020

# Days encoding: 0 = Monday, 1 = Tuesday, 2 = Wednesday
candidate_days = [0, 1, 2]

# Janet's calendar is free all week, so no busy intervals.
# Randy's busy schedule in minutes from midnight
# Monday:   9:00 to 11:00 -> (540, 660), 14:00 to 16:00 -> (840, 960)
# Tuesday:  9:00 to 10:30 -> (540, 630), 11:30 to 12:00 -> (690, 720),
#           14:00 to 14:30 -> (840, 870), 16:00 to 16:30 -> (960, 990)
# Wednesday: 9:00 to 14:00 -> (540, 840), 15:00 to 17:00 -> (900, 1020)
randy_busy = {
    0: [(540, 660), (840, 960)],
    1: [(540, 630), (690, 720), (840, 870), (960, 990)],
    2: [(540, 840), (900, 1020)]
}

# Helper function: ensuring meeting interval [start, start+duration) does not conflict with a busy interval [busy_start, busy_end).
def non_overlap(busy_start, busy_end):
    return Or(start + duration <= busy_start, start >= busy_end)

found = False
meeting_day = None       # day when meeting is scheduled
meeting_start_val = None # meeting start time (in minutes from midnight)

# Iterate over candidate days in order (Monday, then Tuesday, then Wednesday)
for day in candidate_days:
    solver = Solver()
    # The meeting must be within work hours.
    solver.add(start >= WORK_START, start + duration <= WORK_END)
    
    # For Janet, there are no busy constraints.
    
    # Add Randy's busy constraints for the given day.
    for busy_interval in randy_busy.get(day, []):
        busy_start, busy_end = busy_interval
        solver.add(non_overlap(busy_start, busy_end))
    
    # Check minute-by-minute for the earliest available start time.
    for t in range(WORK_START, WORK_END - duration + 1):
        solver.push()
        solver.add(start == t)
        if solver.check() == sat:
            meeting_start_val = t
            meeting_day = day
            found = True
            solver.pop()
            break
        solver.pop()
    
    if found:
        break

if found:
    meeting_end_val = meeting_start_val + duration
    start_hour, start_min = divmod(meeting_start_val, 60)
    end_hour, end_min = divmod(meeting_end_val, 60)
    day_name = {0: "Monday", 1: "Tuesday", 2: "Wednesday"}.get(meeting_day, "Unknown")
    print(f"A valid meeting time is on {day_name} from {start_hour:02d}:{start_min:02d} to {end_hour:02d}:{end_min:02d}.")
else:
    print("No valid meeting time could be found that meets all constraints.")