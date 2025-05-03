from z3 import Solver, Int, Or, sat

# Meeting parameters:
duration = 30  # meeting duration in minutes (half an hour)
start = Int("start")  # meeting start time in minutes from midnight

# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
WORK_START = 540
WORK_END = 1020

# Busy schedules for each participant on Monday (day 0) and Tuesday (day 1)

# Tyler's busy schedule in minutes (from midnight)
# Monday: 9:30 to 10:00 -> (570,600)
# Tuesday: 14:30 to 16:00 -> (870,960)
tyler_busy = {
    0: [(570, 600)],
    1: [(870, 960)]
}

# Marie's busy schedule in minutes (from midnight)
# Monday:
#   9:00 to 10:00   -> (540,600)
#   11:00 to 11:30  -> (660,690)
#   12:30 to 14:00  -> (750,840)
#   14:30 to 15:00  -> (870,900)
#   16:30 to 17:00  -> (990,1020)
# Tuesday:
#   9:30 to 10:30   -> (570,630)
#   11:00 to 12:30  -> (660,750)
#   13:00 to 15:00  -> (780,900)
#   15:30 to 17:00  -> (930,1020)
marie_busy = {
    0: [(540,600), (660,690), (750,840), (870,900), (990,1020)],
    1: [(570,630), (660,750), (780,900), (930,1020)]
}

# Marie's additional constraint on Monday is that she cannot meet after 13:00.
# This means if the meeting is scheduled on Monday, it must finish by 13:00.
# 13:00 in minutes is 780. Thus, for Monday (day 0), we must have: start + duration <= 780.

# Helper function: meeting [start, start+duration) must not overlap a busy interval [b_start, b_end)
def non_overlap(b_start, b_end):
    return Or(start + duration <= b_start, start >= b_end)

found = False
meeting_day = None  # 0 for Monday, 1 for Tuesday
meeting_start = None

# We'll try both days (Monday as day 0 and Tuesday as day 1).
# The order can be arbitrary. Here we try Monday first then Tuesday.
for day in [0, 1]:
    solver = Solver()
    
    # Meeting must be within work hours
    solver.add(start >= WORK_START, start + duration <= WORK_END)
    
    # If it's Monday, add Marie's extra constraint (finish by 13:00)
    if day == 0:
        solver.add(start + duration <= 780)
    
    # Add Tyler's busy constraints
    for b_start, b_end in tyler_busy.get(day, []):
        solver.add(non_overlap(b_start, b_end))
    
    # Add Marie's busy constraints
    for b_start, b_end in marie_busy.get(day, []):
        solver.add(non_overlap(b_start, b_end))
    
    # Try possible start times in ascending order within a feasible search interval.
    # For Monday, note the extra constraint forces start <= 750, but for Tuesday, it's up to WORK_END - duration.
    start_time_min = WORK_START
    start_time_max = WORK_END - duration
    # For Monday (day 0), we can further restrict the search:
    if day == 0:
        start_time_max = min(start_time_max, 780 - duration)
    
    for t in range(start_time_min, start_time_max + 1):
        solver.push()
        solver.add(start == t)
        if solver.check() == sat:
            meeting_start = t
            meeting_day = day
            found = True
            solver.pop()  # remove the temporary assignment for t
            break
        solver.pop()
    
    if found:
        break

if found:
    meeting_end = meeting_start + duration
    # Convert minutes to HH:MM format
    start_hour, start_min = divmod(meeting_start, 60)
    end_hour, end_min = divmod(meeting_end, 60)
    day_str = "Monday" if meeting_day == 0 else "Tuesday"
    print(f"A valid meeting time is on {day_str} from {start_hour:02d}:{start_min:02d} to {end_hour:02d}:{end_min:02d}.")
else:
    print("No valid meeting time could be found that meets all constraints.")