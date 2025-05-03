from z3 import Solver, Int, Or, sat

# Meeting parameters:
duration = 30  # meeting duration in minutes (half an hour)
start = Int("start")  # meeting start time in minutes from midnight

# Work hours: from 9:00 (540 minutes) to 17:00 (1020 minutes)
WORK_START = 540
WORK_END = 1020

# Busy schedules (times expressed in minutes from midnight):

# Jack's busy schedule:
# Monday (day 0):
#   9:30 to 10:00 -> (570, 600)
#   12:30 to 13:30 -> (750, 810)
#   14:00 to 15:00 -> (840, 900)
#   16:00 to 16:30 -> (960, 990)
# Tuesday (day 1):
#   9:00 to 9:30   -> (540, 570)
#   12:00 to 13:30 -> (720, 810)
#   14:30 to 15:00 -> (870, 900)
#   16:00 to 16:30 -> (960, 990)
jack_busy = {
    0: [(570, 600), (750, 810), (840, 900), (960, 990)],
    1: [(540, 570), (720, 810), (870, 900), (960, 990)]
}

# Juan's busy schedule:
# Monday (day 0):
#   10:30 to 12:00 -> (630, 720)
#   13:00 to 13:30 -> (780, 810)
#   14:30 to 15:00 -> (870, 900)
#   15:30 to 16:00 -> (930, 960)
#   16:30 to 17:00 -> (990, 1020)
# Tuesday (day 1):
#   9:30 to 10:00   -> (570, 600)
#   10:30 to 11:00  -> (630, 660)
#   12:00 to 13:00  -> (720, 780)
#   13:30 to 14:30  -> (810, 870)
#   15:30 to 17:00  -> (930, 1020)
juan_busy = {
    0: [(630, 720), (780, 810), (870, 900), (930, 960), (990, 1020)],
    1: [(570, 600), (630, 660), (720, 780), (810, 870), (930, 1020)]
}

# Additional preferences:
# - Jack does NOT want to meet on Tuesday => Disallow meetings on day 1.
# - Juan cannot meet on Monday after 13:00 => For Monday (day 0) the meeting must finish by 13:00 (i.e. start + duration <= 780).

# Helper function to state that the meeting interval [start, start+duration)
# does not overlap with a busy interval [busy_start, busy_end)
def non_overlap(busy_start, busy_end):
    return Or(start + duration <= busy_start, start >= busy_end)

found = False
meeting_day = None  # 0 for Monday, 1 for Tuesday
meeting_start = None

# Try days in order: Monday (day 0) then Tuesday (day 1)
for day in [0, 1]:
    solver = Solver()
    # Enforce meeting time within work hours:
    solver.add(start >= WORK_START, start + duration <= WORK_END)
    
    if day == 0:
        # Apply Juan's preference: on Monday meeting must finish by 13:00 (780 minutes)
        solver.add(start + duration <= 780)
    elif day == 1:
        # Jack does not want to meet on Tuesday; disallow scheduling on Tuesday.
        solver.add(False)
    
    # Add Jack's busy intervals for the day.
    for b_start, b_end in jack_busy.get(day, []):
        solver.add(non_overlap(b_start, b_end))
        
    # Add Juan's busy intervals for the day.
    for b_start, b_end in juan_busy.get(day, []):
        solver.add(non_overlap(b_start, b_end))
    
    # Try possible start times minute-by-minute.
    for t in range(WORK_START, WORK_END - duration + 1):
        solver.push()
        solver.add(start == t)
        if solver.check() == sat:
            meeting_start = t
            meeting_day = day
            found = True
            solver.pop()  # remove the temporary constraint before breaking out
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