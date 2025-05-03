from z3 import Solver, Int, Or, sat

# Meeting parameters
duration = 60  # meeting duration in minutes (1 hour)
start = Int("start")  # meeting start time in minutes from midnight

# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
WORK_START = 540
WORK_END = 1020

# Days encoding: 0 = Monday, 1 = Tuesday, 2 = Wednesday
# However, Grace does not want to meet on Wednesday, so candidates are only Monday and Tuesday.
candidate_days = [0, 1]

# Grace's busy schedule in minutes from midnight:
# Monday: 9:00 to 9:30 -> (540, 570)
# Wednesday: 16:00 to 16:30 -> (960, 990)   (but Wednesday is not an option per Grace's preference)
grace_busy = {
    0: [(540, 570)],
    2: [(960, 990)]
}

# Dennis's busy schedule in minutes from midnight:
# Monday:    9:00 to 11:00 -> (540, 660), 11:30 to 12:00 -> (690, 720), 
#            12:30 to 13:00 -> (750, 780), 13:30 to 15:30 -> (810, 930), 16:00 to 17:00 -> (960, 1020)
# Tuesday:   9:00 to 10:30 -> (540, 630), 11:00 to 11:30 -> (660, 690), 
#            12:00 to 14:00 -> (720, 840), 14:30 to 16:00 -> (870, 960)
# Wednesday: 9:00 to 10:00 -> (540, 600), 10:30 to 12:30 -> (630, 750), 
#            14:00 to 16:00 -> (840, 960), 16:30 to 17:00 -> (990, 1020)
dennis_busy = {
    0: [(540, 660), (690, 720), (750, 780), (810, 930), (960, 1020)],
    1: [(540, 630), (660, 690), (720, 840), (870, 960)],
    2: [(540, 600), (630, 750), (840, 960), (990, 1020)]
}

# Helper function: The meeting interval [start, start+duration) must not overlap 
# with a busy interval [busy_start, busy_end).
def non_overlap(busy_start, busy_end):
    return Or(start + duration <= busy_start, start >= busy_end)

found = False
meeting_day = None       # day when meeting is scheduled (0 for Monday, 1 for Tuesday)
meeting_start_val = None # meeting start time in minutes from midnight

# Iterate over candidate days in order.
for day in candidate_days:
    solver = Solver()
    
    # Ensure the meeting is within work hours.
    solver.add(start >= WORK_START, start + duration <= WORK_END)
    
    # Apply Grace's day preference:
    # Even though Grace has a busy interval on Wednesday, she doesn't want that day.
    # So, if day is Wednesday we would add: solver.add(False)
    # But candidate_days does not include Wednesday.
    
    # Add Grace's busy constraints if any for the current day.
    for busy_interval in grace_busy.get(day, []):
        busy_start, busy_end = busy_interval
        solver.add(non_overlap(busy_start, busy_end))
    
    # Add Dennis's busy constraints for the current day.
    for busy_start, busy_end in dennis_busy.get(day, []):
        solver.add(non_overlap(busy_start, busy_end))
    
    # Search for the earliest possible time slot (minute-by-minute).
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