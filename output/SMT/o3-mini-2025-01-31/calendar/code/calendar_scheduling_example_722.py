from z3 import Solver, Int, Or, sat

# Meeting parameters
duration = 60  # meeting duration in minutes (1 hour)
start = Int("start")  # meeting start time in minutes from midnight

# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
WORK_START = 540
WORK_END = 1020

# Days encoding: 0 = Monday, 1 = Tuesday, 2 = Wednesday
# Zachary would like to avoid Tuesday so we only consider Monday and Wednesday.
allowed_days = [0, 2]

# Busy schedules for each participant (times in minutes from midnight)

# Elijah's busy schedule:
# Monday:   13:00 to 13:30  -> (780, 810)
# Tuesday:  14:30 to 15:00  -> (870, 900)   [but Tuesday is avoided]
# Wednesday: 10:30 to 11:00  -> (630, 660)
#            13:00 to 13:30 -> (780, 810)
elijah_busy = {
    0: [(780, 810)],
    1: [(870, 900)],  # We'll not consider Tuesday as allowed
    2: [(630, 660), (780, 810)]
}

# Zachary's busy schedule:
# Monday:   9:00 to 12:00   -> (540, 720)
#           13:30 to 14:30  -> (810, 870)
#           15:00 to 16:00  -> (900, 960)
#           16:30 to 17:00  -> (990, 1020)
# Tuesday:  9:00 to 9:30    -> (540, 570)
#           10:00 to 11:00  -> (600, 660)
#           12:00 to 14:30  -> (720, 870)
#           15:00 to 16:00  -> (900, 960)
#           16:30 to 17:00  -> (990, 1020)
# Wednesday:10:30 to 15:00   -> (630, 900)
#           16:00 to 16:30  -> (960, 990)
zachary_busy = {
    0: [(540, 720), (810, 870), (900, 960), (990, 1020)],
    1: [(540, 570), (600, 660), (720, 870), (900, 960), (990, 1020)],
    2: [(630, 900), (960, 990)]
}

# Helper function: meeting interval [start, start+duration) must not overlap with a busy interval [busy_start, busy_end)
def non_overlap(busy_start, busy_end):
    return Or(start + duration <= busy_start, start >= busy_end)

found = False
meeting_day = None         # will store the day (0: Monday, 2: Wednesday) when meeting is scheduled
meeting_start_val = None   # meeting start time in minutes from midnight

# Iterate over allowed days in order (Monday first, then Wednesday)
for day in allowed_days:
    solver = Solver()
    # Constraint: meeting must be within work hours.
    solver.add(start >= WORK_START, start + duration <= WORK_END)
    
    # Add Elijah's busy constraints for the given day.
    for busy_start, busy_end in elijah_busy.get(day, []):
        solver.add(non_overlap(busy_start, busy_end))
    
    # Add Zachary's busy constraints for the given day.
    for busy_start, busy_end in zachary_busy.get(day, []):
        solver.add(non_overlap(busy_start, busy_end))
    
    # Find the earliest valid start time (checking minute-by-minute)
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
    # Convert minutes to HH:MM format.
    start_hour, start_min = divmod(meeting_start_val, 60)
    end_hour, end_min = divmod(meeting_end_val, 60)
    day_name = {0: "Monday", 2: "Wednesday"}.get(meeting_day, "Unknown")
    print(f"A valid meeting time is on {day_name} from {start_hour:02d}:{start_min:02d} to {end_hour:02d}:{end_min:02d}.")
else:
    print("No valid meeting time could be found that meets all constraints.")