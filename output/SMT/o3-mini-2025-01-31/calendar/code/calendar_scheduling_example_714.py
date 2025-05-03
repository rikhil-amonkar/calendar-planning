from z3 import Solver, Int, Or, sat

# Meeting parameters
duration = 30  # meeting duration in minutes
start = Int("start")  # meeting start time in minutes from midnight

# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
WORK_START = 540
WORK_END = 1020

# Days encoding: 0 = Monday, 1 = Tuesday, 2 = Wednesday
# According to constraints:
#   • Zachary cannot meet on Monday after 12:30 and cannot meet on Wednesday.
#   • Debra would rather not meet on Tuesday (preference).
# Thus we try Monday first, then Tuesday.
allowed_days = [0, 1]

# Busy schedules are represented as lists of intervals (start, end) in minutes.
# Convert times to minutes-from-midnight.

# Zachary's busy schedule:
zachary_busy = {
    0: [ (12 * 60, 12 * 60 + 30),  # Monday: 12:00 to 12:30 -> (720,750)
         (14 * 60 + 30, 15 * 60) ], # Monday: 14:30 to 15:00 -> (870,900)
    1: [ (9 * 60 + 30, 10 * 60),    # Tuesday: 9:30 to 10:00 -> (570,600)
         (11 * 60 + 30, 12 * 60),   # Tuesday: 11:30 to 12:00 -> (690,720)
         (15 * 60 + 30, 16 * 60) ], # Tuesday: 15:30 to 16:00 -> (930,960)
    2: [ (11 * 60 + 30, 12 * 60) ]  # Wednesday: 11:30 to 12:00 -> (690,720) (but not allowed)
}

# Debra's busy schedule:
debra_busy = {
    0: [ (9 * 60 + 30, 11 * 60),   # Monday: 9:30 to 11:00 -> (570,660)
         (11 * 60 + 30, 12 * 60),  # Monday: 11:30 to 12:00 -> (690,720)
         (13 * 60, 13 * 60 + 30),  # Monday: 13:00 to 13:30 -> (780,810)
         (14 * 60, 17 * 60) ],     # Monday: 14:00 to 17:00 -> (840,1020)
    1: [ (9 * 60, 14 * 60 + 30),   # Tuesday: 9:00 to 14:30 -> (540,870)
         (15 * 60, 17 * 60) ],      # Tuesday: 15:00 to 17:00 -> (900,1020)
    2: [ (9 * 60, 10 * 60),        # Wednesday: 9:00 to 10:00 -> (540,600)
         (11 * 60, 13 * 60 + 30),   # Wednesday: 11:00 to 13:30 -> (660,810)
         (14 * 60, 15 * 60 + 30),   # Wednesday: 14:00 to 15:30 -> (840,930)
         (16 * 60, 17 * 60) ]       # Wednesday: 16:00 to 17:00 -> (960,1020)
}

# Helper function: meeting [start, start+duration) must not overlap with busy interval [busy_start, busy_end)
def non_overlap(busy_start, busy_end):
    return Or(start + duration <= busy_start, start >= busy_end)

found = False
meeting_day = None   # day code (0: Monday, 1: Tuesday)
meeting_start_val = None  # meeting start time in minutes

# We search over allowed days in order. Since Debra prefers not to meet on Tuesday,
# we check Monday first.
for day in allowed_days:
    solver = Solver()
    # The meeting must be within work hours.
    solver.add(start >= WORK_START, start + duration <= WORK_END)
    
    # Additional constraint for Zachary on Monday:
    # "cannot meet on Monday after 12:30" means if meeting is on Monday (day 0) then it must end by 12:30.
    if day == 0:
        solver.add(start + duration <= 12 * 60 + 30)  # meeting ends by 12:30 (i.e. <=750)
        
    # (For Tuesday, no extra time constraint is needed.)
    
    # Add non-overlap constraints for each participant's busy intervals.
    # For Zachary:
    for (b_start, b_end) in zachary_busy.get(day, []):
        solver.add(non_overlap(b_start, b_end))
    # For Debra:
    for (b_start, b_end) in debra_busy.get(day, []):
        solver.add(non_overlap(b_start, b_end))
    
    # Iterate over possible start times (minute-by-minute) for the earliest solution.
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