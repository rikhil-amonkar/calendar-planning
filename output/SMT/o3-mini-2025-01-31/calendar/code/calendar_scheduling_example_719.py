from z3 import Solver, Int, Or, sat

# Meeting parameters
duration = 60  # meeting duration in minutes
start = Int("start")  # meeting start time in minutes from midnight

# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
WORK_START = 540
WORK_END = 1020

# Days encoding: 0 = Monday, 1 = Tuesday, 2 = Wednesday
allowed_days = [0, 1, 2]

# Busy schedules for each participant (intervals in minutes from midnight)
# Hannah is free the entire week, so no busy intervals for her.

# Teresa's busy schedule:
# Monday: 9:00-11:00, 12:00-14:30, 15:00-17:00
# Tuesday: 9:00-17:00 (fully busy)
# Wednesday: 9:00-12:00, 12:30-14:00, 14:30-16:30
teresa_busy = {
    0: [(9*60, 11*60), (12*60, 14*60+30), (15*60, 17*60)],
    1: [(9*60, 17*60)],  # entire day busy
    2: [(9*60, 12*60), (12*60+30, 14*60), (14*60+30, 16*60+30)]
}

# Helper function: ensures the meeting [start, start+duration) does NOT overlap with a busy interval [busy_start, busy_end)
def non_overlap(busy_start, busy_end):
    return Or(start + duration <= busy_start, start >= busy_end)

found = False
meeting_day = None         # day where meeting is scheduled (0, 1, or 2)
meeting_start_val = None   # meeting start time in minutes from midnight

# Iterate over allowed days in order (earlier day first)
for day in allowed_days:
    solver = Solver()
    # Meeting must occur within work hours.
    solver.add(start >= WORK_START, start + duration <= WORK_END)
    
    # Add Teresa's busy schedule constraints for the current day.
    for busy_start, busy_end in teresa_busy.get(day, []):
        solver.add(non_overlap(busy_start, busy_end))
    
    # Since Hannah is free, no constraints for her.
    
    # Iterate through each possible starting minute to find the earliest valid meeting time.
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
    # Convert minutes into HH:MM format.
    start_hour, start_min = divmod(meeting_start_val, 60)
    end_hour, end_min = divmod(meeting_end_val, 60)
    day_name = {0: "Monday", 1: "Tuesday", 2: "Wednesday"}.get(meeting_day, "Unknown")
    print(f"A valid meeting time is on {day_name} from {start_hour:02d}:{start_min:02d} to {end_hour:02d}:{end_min:02d}.")
else:
    print("No valid meeting time could be found that meets all constraints.")