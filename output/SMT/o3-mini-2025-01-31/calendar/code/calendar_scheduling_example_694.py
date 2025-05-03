from z3 import Solver, Int, Or, sat

# Meeting parameters:
duration = 30  # duration in minutes (half an hour)
start = Int("start")  # meeting start time in minutes from midnight

# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
WORK_START = 540
WORK_END = 1020

# Patrick's busy schedule (times in minutes from midnight)
# Monday (day 0):
#   10:00 to 10:30  -> (600, 630)
#   12:00 to 14:00  -> (720, 840)
#   14:30 to 15:30  -> (870, 930)
#   16:00 to 17:00  -> (960, 1020)
# Tuesday (day 1):
#   9:00 to 9:30    -> (540, 570)
#   10:30 to 11:00  -> (630, 660)
#   14:30 to 15:00  -> (870, 900)
patrick_busy = {
    0: [(600, 630), (720, 840), (870, 930), (960, 1020)],
    1: [(540, 570), (630, 660), (870, 900)]
}

# Lawrence's busy schedule (times in minutes from midnight)
# Monday (day 0):
#   9:00 to 13:00   -> (540, 780)
#   13:30 to 16:00  -> (810, 960)
#   16:30 to 17:00  -> (990, 1020)
# Tuesday (day 1):
#   9:00 to 10:00   -> (540, 600)
#   10:30 to 12:30  -> (630, 750)
#   13:00 to 15:30  -> (780, 930)
#   16:30 to 17:00  -> (990, 1020)
lawrence_busy = {
    0: [(540, 780), (810, 960), (990, 1020)],
    1: [(540, 600), (630, 750), (780, 930), (990, 1020)]
}

# Extra constraint:
# Patrick cannot meet on Tuesday before 15:30 (i.e. before 930 minutes)
def add_extra_constraints(solver, day):
    if day == 1:
        solver.add(start >= 930)

# Helper function to ensure that the meeting [start, start+duration)
# does not overlap with an occupied time interval [busy_start, busy_end)
def non_overlap(busy_start, busy_end):
    return Or(start + duration <= busy_start, start >= busy_end)

found = False
meeting_day = None  # 0: Monday, 1: Tuesday
meeting_start = None

# Try scheduling on Monday (day 0) first, then Tuesday (day 1)
for day in [0, 1]:
    solver = Solver()
    # Meeting must be within work hours.
    solver.add(start >= WORK_START, start + duration <= WORK_END)
    
    # Add busy constraints for Patrick.
    for b_start, b_end in patrick_busy.get(day, []):
        solver.add(non_overlap(b_start, b_end))
    
    # Add busy constraints for Lawrence.
    for b_start, b_end in lawrence_busy.get(day, []):
        solver.add(non_overlap(b_start, b_end))
    
    # Add extra constraint (for Tuesday, Patrick cannot meet before 15:30).
    add_extra_constraints(solver, day)
    
    # Try potential start times in order (earlier times first)
    for t in range(WORK_START, WORK_END - duration + 1):
        solver.push()
        solver.add(start == t)
        if solver.check() == sat:
            meeting_start = t
            meeting_day = day
            found = True
            solver.pop()  # remove the temporary constraint for t
            break
        solver.pop()
    
    if found:
        break

if found:
    meeting_end = meeting_start + duration
    # Convert minutes to HH:MM format.
    start_hour, start_min = divmod(meeting_start, 60)
    end_hour, end_min = divmod(meeting_end, 60)
    day_str = "Monday" if meeting_day == 0 else "Tuesday"
    print(f"A valid meeting time is on {day_str} from {start_hour:02d}:{start_min:02d} to {end_hour:02d}:{end_min:02d}.")
else:
    print("No valid meeting time could be found that meets all constraints.")