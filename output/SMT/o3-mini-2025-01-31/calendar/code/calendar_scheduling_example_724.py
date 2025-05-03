from z3 import Solver, Int, Or, sat

# Meeting parameters
duration = 30  # meeting duration in minutes (half an hour)
start = Int("start")  # meeting start time in minutes from midnight

# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
WORK_START = 540
WORK_END = 1020

# Days encoding: 0 = Monday, 1 = Tuesday, 2 = Wednesday
allowed_days = [0, 1, 2]

# Tyler's busy schedule (in minutes from midnight)
# Provided busy times:
# Tuesday: 9:00 to 9:30  -> (540, 570), and 14:30 to 15:00 -> (870, 900)
# Wednesday: 10:30 to 11:00 -> (630, 660), 12:30 to 13:00 -> (750, 780),
#            13:30 to 14:00 -> (810, 840), 16:30 to 17:00 -> (990, 1020)
tyler_busy = {
    1: [(540, 570), (870, 900)],
    2: [(630, 660), (750, 780), (810, 840), (990, 1020)]
}

# Ruth's busy schedule (in minutes from midnight)
# Monday:    9:00 to 10:00   -> (540, 600),
#            10:30 to 12:00  -> (630, 720),
#            12:30 to 14:30  -> (750, 870),
#            15:00 to 16:00  -> (900, 960),
#            16:30 to 17:00  -> (990, 1020)
# Tuesday:   9:00 to 17:00   -> (540, 1020)
# Wednesday: 9:00 to 17:00   -> (540, 1020)
ruth_busy = {
    0: [(540, 600), (630, 720), (750, 870), (900, 960), (990, 1020)],
    1: [(540, 1020)],
    2: [(540, 1020)]
}

# Tyler's additional preference: On Monday (day 0), he would like to avoid meetings before 16:00 (i.e., before 960 minutes).
def tyler_monday_preference(day):
    if day == 0:
        return start >= 16 * 60  # 16:00 in minutes
    return True

# Helper function: meeting interval [start, start+duration) must not overlap with a busy interval [busy_start, busy_end)
def non_overlap(busy_start, busy_end):
    return Or(start + duration <= busy_start, start >= busy_end)

found = False
meeting_day = None       # will hold the day (0 = Monday, 1 = Tuesday, 2 = Wednesday) when the meeting is scheduled
meeting_start_val = None # meeting start time in minutes from midnight

# Try each allowed day in order (earliest day first)
for day in allowed_days:
    solver = Solver()
    # Meeting must be within work hours.
    solver.add(start >= WORK_START, start + duration <= WORK_END)
    
    # Add Tyler's additional preference for Monday.
    solver.add(tyler_monday_preference(day))
    
    # Add Tyler's busy intervals for the given day.
    for busy_start, busy_end in tyler_busy.get(day, []):
        solver.add(non_overlap(busy_start, busy_end))
    
    # Add Ruth's busy intervals for the given day.
    for busy_start, busy_end in ruth_busy.get(day, []):
        solver.add(non_overlap(busy_start, busy_end))
    
    # Determine the starting time for iteration.
    # If day is Monday, Tyler's preference already enforces start>=960, so iterate accordingly.
    start_time = WORK_START
    if day == 0:
        start_time = max(WORK_START, 16 * 60)  # 16:00 in minutes

    # Find the earliest valid start time (minute-by-minute)
    for t in range(start_time, WORK_END - duration + 1):
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
    # Convert times from minutes to HH:MM format.
    start_hour, start_min = divmod(meeting_start_val, 60)
    end_hour, end_min = divmod(meeting_end_val, 60)
    day_name = {0: "Monday", 1: "Tuesday", 2: "Wednesday"}.get(meeting_day, "Unknown")
    print(f"A valid meeting time is on {day_name} from {start_hour:02d}:{start_min:02d} to {end_hour:02d}:{end_min:02d}.")
else:
    print("No valid meeting time could be found that meets all constraints.")