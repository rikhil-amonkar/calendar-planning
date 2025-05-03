from z3 import Solver, Int, Or, sat

# Meeting parameters:
duration = 30  # meeting duration in minutes (half an hour)
start = Int("start")  # meeting start time in minutes from midnight

# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
WORK_START = 540
WORK_END = 1020

# Busy schedules (times in minutes from midnight):

# Elizabeth's busy schedule:
# Monday (day 0):
#   12:00 to 12:30 -> (720, 750)
#   13:00 to 13:30 -> (780, 810)
#   14:00 to 14:30 -> (840, 870)
#   15:30 to 16:00 -> (930, 960)
# Tuesday (day 1):
#   10:30 to 11:00 -> (630, 660)
#   15:30 to 16:00 -> (930, 960)
elizabeth_busy = {
    0: [(720, 750), (780, 810), (840, 870), (930, 960)],
    1: [(630, 660), (930, 960)]
}

# Mason's busy schedule:
# Monday (day 0):
#   9:00 to 15:00  -> (540, 900)
#   15:30 to 17:00 -> (930, 1020)
# Tuesday (day 1):
#   9:00 to 16:30  -> (540, 990)
mason_busy = {
    0: [(540, 900), (930, 1020)],
    1: [(540, 990)]
}

# Additional preference:
# - Elizabeth does not want to meet on Monday.
#   (We enforce Monday to be invalid)

# Helper function to ensure the meeting
# [start, start+duration) does not overlap with a busy interval [busy_start, busy_end)
def non_overlap(busy_start, busy_end):
    return Or(start + duration <= busy_start, start >= busy_end)

found = False
meeting_day = None  # 0 for Monday, 1 for Tuesday
meeting_start = None

# We try days Monday (day 0) then Tuesday (day 1)
for day in [0, 1]:
    solver = Solver()
    
    # Meeting must be within work hours.
    solver.add(start >= WORK_START, start + duration <= WORK_END)
    
    if day == 0:
        # Elizabeth does not want to meet on Monday.
        solver.add(False)
    
    # Add Elizabeth's busy intervals for the day.
    for b_start, b_end in elizabeth_busy.get(day, []):
        solver.add(non_overlap(b_start, b_end))
    
    # Add Mason's busy intervals for the day.
    for b_start, b_end in mason_busy.get(day, []):
        solver.add(non_overlap(b_start, b_end))
    
    # Try possible start times from the beginning of work hours to the latest possible start.
    for t in range(WORK_START, WORK_END - duration + 1):
        solver.push()
        solver.add(start == t)
        if solver.check() == sat:
            meeting_start = t
            meeting_day = day
            found = True
            solver.pop()  # Remove the temporary constraint.
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