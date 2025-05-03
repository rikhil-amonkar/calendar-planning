from z3 import Solver, Int, Or, sat

# Meeting parameters
duration = 60  # meeting duration in minutes (1 hour)
start = Int("start")  # meeting start time in minutes from midnight

# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
WORK_START = 540
WORK_END = 1020

# Days encoding: 0 = Monday, 1 = Tuesday, 2 = Wednesday
candidate_days = [0, 1, 2]

# Heather is free the entire week, so she has no busy slots.
# Dennis's busy schedule in minutes from midnight:
# Monday:    9:00 to 17:00  -> (540, 1020)
# Tuesday:   9:00 to 11:30  -> (540, 690), 13:00 to 13:30 -> (780, 810), 
#            14:00 to 15:30 -> (840, 930), 16:00 to 17:00 -> (960, 1020)
# Wednesday: 9:00 to 9:30   -> (540, 570), 10:00 to 17:00 -> (600, 1020)
dennis_busy = {
    0: [(540, 1020)],
    1: [(540, 690), (780, 810), (840, 930), (960, 1020)],
    2: [(540, 570), (600, 1020)]
}

# Helper function:
# The meeting interval [start, start+duration) must not overlap with a busy interval [busy_start, busy_end).
def non_overlap(busy_start, busy_end):
    return Or(start + duration <= busy_start, start >= busy_end)

found = False
meeting_day = None       # day when meeting is scheduled (0, 1, or 2)
meeting_start_val = None # meeting start time in minutes from midnight

# Check candidate days in order.
for day in candidate_days:
    solver = Solver()
    # Ensure the meeting is scheduled within work hours.
    solver.add(start >= WORK_START, start + duration <= WORK_END)
    
    # Add Dennis's busy constraints for the day.
    for busy_start, busy_end in dennis_busy.get(day, []):
        solver.add(non_overlap(busy_start, busy_end))
    
    # Heather is free, so no constraints needed for her.
    
    # Search for the earliest possible start time (minute-by-minute)
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