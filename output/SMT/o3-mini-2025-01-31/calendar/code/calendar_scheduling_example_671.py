from z3 import Solver, Int, Or, sat

# Meeting parameters:
duration = 60  # meeting duration in minutes (one hour)
start = Int("start")  # meeting start time in minutes from midnight

# Work hours: from 9:00 (540 minutes) to 17:00 (1020 minutes)
WORK_START = 540
WORK_END = 1020

# Busy schedules (times in minutes from midnight):

# Anthony's busy schedule:
# Monday (day 0):
#   12:00 to 12:30 -> (720, 750)
#   13:30 to 14:00 -> (810, 840)
# Tuesday (day 1):
#   10:00 to 10:30 -> (600, 630)
#   11:30 to 12:00 -> (690, 720)
#   13:00 to 13:30 -> (780, 810)
#   16:30 to 17:00 -> (990, 1020)
anthony_busy = {
    0: [(720, 750), (810, 840)],
    1: [(600, 630), (690, 720), (780, 810), (990, 1020)]
}

# Jacob's busy schedule:
# Monday (day 0):
#    9:00 to 10:00  -> (540, 600)
#   11:00 to 12:00  -> (660, 720)
#   12:30 to 15:00  -> (750, 900)
#   15:30 to 16:00  -> (930, 960)
#   16:30 to 17:00  -> (990, 1020)
# Tuesday (day 1):
#   10:30 to 12:00  -> (630, 720)
#   12:30 to 13:00  -> (750, 780)
#   15:00 to 15:30  -> (900, 930)
#   16:00 to 17:00  -> (960, 1020)
jacob_busy = {
    0: [(540, 600), (660, 720), (750, 900), (930, 960), (990, 1020)],
    1: [(630, 720), (750, 780), (900, 930), (960, 1020)]
}

# Additional preferences:
# - Anthony cannot meet on Tuesday.
# - (No extra time-of-day preferences were given for Jacob.)

# Define helper function to ensure that the meeting interval [start, start+duration)
# does not overlap with a busy interval [busy_start, busy_end)
def non_overlap(busy_start, busy_end):
    return Or(start + duration <= busy_start, start >= busy_end)

found = False
meeting_day = None  # 0 for Monday, 1 for Tuesday
meeting_start = None

# Loop over possible days: Monday (day 0), then Tuesday (day 1)
for day in [0, 1]:
    solver = Solver()
    
    # Constrain meeting to be completely within work hours.
    solver.add(start >= WORK_START, start + duration <= WORK_END)
    
    # Anthony cannot meet on Tuesday.
    if day == 1:
        solver.add(False)
    
    # Add Anthony's busy intervals for the day.
    for b_start, b_end in anthony_busy.get(day, []):
        solver.add(non_overlap(b_start, b_end))
    
    # Add Jacob's busy intervals for the day.
    for b_start, b_end in jacob_busy.get(day, []):
        solver.add(non_overlap(b_start, b_end))
    
    # We iterate over all possible start times (in minutes).
    for t in range(WORK_START, WORK_END - duration + 1):
        solver.push()
        solver.add(start == t)
        if solver.check() == sat:
            meeting_start = t
            meeting_day = day
            found = True
            solver.pop()  # Clean up the temporary constraint.
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