from z3 import Solver, Int, Or, sat

# Meeting parameters
duration = 30  # meeting duration in minutes
start = Int("start")  # meeting start time in minutes from midnight

# Work hours: 9:00 (540) to 17:00 (1020)
WORK_START = 540
WORK_END = 1020

# Busy schedules (in minutes from midnight):

# Charles' busy schedule:
# Monday:
#   10:00 to 11:00 -> (600, 660)
#   12:00 to 12:30 -> (720, 750)
#   13:30 to 14:00 -> (810, 840)
#   15:00 to 15:30 -> (900, 930)
#   16:00 to 17:00 -> (960, 1020)
# Tuesday:
#   12:00 to 12:30 -> (720, 750)
#   13:00 to 14:00 -> (780, 840)
#   14:30 to 15:00 -> (870, 900)
#   16:30 to 17:00 -> (990, 1020)
charles_busy = {
    0: [(600, 660), (720, 750), (810, 840), (900, 930), (960, 1020)],
    1: [(720, 750), (780, 840), (870, 900), (990, 1020)]
}

# Jose's busy schedule:
# Monday:
#   9:00 to 17:00 -> (540, 1020)
# Tuesday:
#   9:00 to 10:00 -> (540, 600)
#   11:00 to 11:30 -> (660, 690)
#   12:00 to 15:30 -> (720, 930)
jose_busy = {
    0: [(540, 1020)],
    1: [(540, 600), (660, 690), (720, 930)]
}

# Additional constraint:
# Charles would like to avoid meetings on Tuesday after 13:30.
# For Tuesday (day 1), we'll add the constraint: meeting start must be before 13:30 (i.e., <810).

# Helper function: ensure meeting interval [start, start+duration) doesn't overlap with a busy interval [busy_start, busy_end)
def non_overlap(busy_start, busy_end):
    return Or(start + duration <= busy_start, start >= busy_end)

found = False
meeting_day = None  # 0 for Monday, 1 for Tuesday
meeting_start = None

# We'll try scheduling for Monday first, then Tuesday.
for day in [0, 1]:
    solver = Solver()
    # Meeting must be within work hours.
    solver.add(start >= WORK_START, start + duration <= WORK_END)
    
    # For Tuesday, apply Charles' additional preference:
    if day == 1:
        solver.add(start < 810)  # Meeting should start before 13:30
    
    # Add Charles' busy constraints
    for (busy_start, busy_end) in charles_busy.get(day, []):
        solver.add(non_overlap(busy_start, busy_end))
    
    # Add Jose's busy constraints
    for (busy_start, busy_end) in jose_busy.get(day, []):
        solver.add(non_overlap(busy_start, busy_end))
    
    # Iterate over possible start times minute by minute.
    for t in range(WORK_START, WORK_END - duration + 1):
        solver.push()
        solver.add(start == t)
        if solver.check() == sat:
            meeting_start = t
            meeting_day = day
            found = True
            solver.pop()
            break
        solver.pop()
    
    if found:
        break

if found:
    meeting_end = meeting_start + duration
    start_hour, start_min = divmod(meeting_start, 60)
    end_hour, end_min = divmod(meeting_end, 60)
    day_str = "Monday" if meeting_day == 0 else "Tuesday"
    print(f"A valid meeting time is on {day_str} from {start_hour:02d}:{start_min:02d} to {end_hour:02d}:{end_min:02d}.")
else:
    print("No valid meeting time could be found that meets all constraints.")