from z3 import Solver, Int, Or, sat

# Meeting parameters
duration = 30  # meeting duration in minutes (half an hour)
start = Int("start")  # meeting start time in minutes from midnight

# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
WORK_START = 540
WORK_END = 1020

# Days encoding: 0 = Monday, 1 = Tuesday, 2 = Wednesday
allowed_days = [0, 1, 2]

# Brittany's busy schedule in minutes from midnight:
# Monday:    9:00-10:00   -> (540, 600)
#            10:30-11:30  -> (630, 690)
#            14:30-15:00  -> (870, 900)
#            16:00-17:00  -> (960,1020)
# Tuesday:   9:00-9:30    -> (540, 570)
#            12:00-12:30  -> (720, 750)
#            13:00-13:30  -> (780, 810)
#            14:30-15:30  -> (870, 930)
#            16:30-17:00  -> (990,1020)
# Wednesday: 9:00-9:30    -> (540, 570)
#            10:30-11:30  -> (630, 690)
#            13:30-14:00  -> (810, 840)
#            16:00-16:30  -> (960, 990)
brittany_busy = {
    0: [(540, 600), (630, 690), (870, 900), (960, 1020)],
    1: [(540, 570), (720, 750), (780, 810), (870, 930), (990, 1020)],
    2: [(540, 570), (630, 690), (810, 840), (960, 990)]
}

# Bruce's busy schedule in minutes from midnight:
# Monday:    9:30-10:00   -> (570, 600)
#            10:30-11:30  -> (630, 690)
#            12:30-15:00  -> (750, 900)
#            15:30-17:00  -> (930, 1020)
# Tuesday:   10:00-10:30  -> (600, 630)
#            11:30-12:00  -> (690, 720)
#            14:30-17:00  -> (870, 1020)
# Wednesday: 12:30-13:00  -> (750, 780)
#            13:30-14:30  -> (810, 870)
#            15:00-16:30  -> (900, 990)
bruce_busy = {
    0: [(570, 600), (630, 690), (750, 900), (930, 1020)],
    1: [(600, 630), (690, 720), (870, 1020)],
    2: [(750, 780), (810, 870), (900, 990)]
}

# Helper function: the meeting interval [start, start+duration) must not overlap a busy interval [busy_start, busy_end)
def non_overlap(busy_start, busy_end):
    return Or(start + duration <= busy_start, start >= busy_end)

# Try each allowed day (earliest day first) and search minute-by-minute for a suitable time.
found = False
meeting_day = None       # holds the day (0, 1, or 2) when meeting is scheduled
meeting_start_val = None # holds the meeting start time in minutes from midnight

for day in allowed_days:
    solver = Solver()
    
    # Meeting must be scheduled entirely within work hours.
    solver.add(start >= WORK_START, start + duration <= WORK_END)
    
    # Add Brittany's busy time constraints for the given day.
    for b_start, b_end in brittany_busy.get(day, []):
        solver.add(non_overlap(b_start, b_end))
        
    # Add Bruce's busy time constraints for the given day.
    for b_start, b_end in bruce_busy.get(day, []):
        solver.add(non_overlap(b_start, b_end))
    
    # Try each possible start time on the day (minute-by-minute)
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
    day_name = {0: "Monday", 1: "Tuesday", 2: "Wednesday"}.get(meeting_day, "Unknown")
    print(f"A valid meeting time is on {day_name} from {start_hour:02d}:{start_min:02d} to {end_hour:02d}:{end_min:02d}.")
else:
    print("No valid meeting time could be found that meets all constraints.")