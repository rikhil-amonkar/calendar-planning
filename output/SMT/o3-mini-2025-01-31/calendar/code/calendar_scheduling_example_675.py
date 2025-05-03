from z3 import Solver, Int, Or, sat

# Meeting parameters:
duration = 60  # meeting duration in minutes (1 hour)
start = Int("start")  # meeting start time in minutes from midnight

# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
WORK_START = 540
WORK_END = 1020

# Busy schedules (times expressed in minutes from midnight):

# Janet's calendar is wide open (no busy intervals).
janet_busy = {
    0: [],  # Monday
    1: []   # Tuesday
}

# Larry's busy schedule:
# Monday (day 0):
#   9:00 to 9:30  -> (540, 570)
#   11:00 to 11:30-> (660, 690)
#   12:00 to 13:30-> (720, 810)
#   14:00 to 16:30-> (840, 990)
# Tuesday (day 1):
#   9:00 to 11:30  -> (540, 690)
#   12:00 to 12:30 -> (720, 750)
#   14:30 to 15:00 -> (870, 900)
#   15:30 to 16:00 -> (930, 960)
larry_busy = {
    0: [(540, 570), (660, 690), (720, 810), (840, 990)],
    1: [(540, 690), (720, 750), (870, 900), (930, 960)]
}

# Additional constraints/Preferences:
# - Larry can not meet on Monday. (So if day is Monday, meeting is invalid.)
# - On Tuesday, Larry cannot meet after 15:30.
#   Since the meeting lasts one hour, on Tuesday the meeting must finish by 15:30.
#   15:30 is 930 minutes from midnight, so on Tuesday we require start + duration <= 930.

# Helper function to ensure that the meeting interval [start, start+duration)
# does not overlap with a given busy interval [busy_start, busy_end)
def non_overlap(busy_start, busy_end):
    # Meeting must finish on or before busy_start or start after busy_end.
    return Or(start + duration <= busy_start, start >= busy_end)

found = False
meeting_day = None  # 0 for Monday, 1 for Tuesday
meeting_start = None

# We try scheduling on Monday (day 0) and Tuesday (day 1)
for day in [0, 1]:
    solver = Solver()
    
    # Meeting must fit inside work hours
    solver.add(start >= WORK_START, start + duration <= WORK_END)
    
    # Apply day-specific constraints:
    if day == 0:
        # Larry does not want meetings on Monday.
        solver.add(False)
    elif day == 1:
        # On Tuesday, Larry cannot meet after 15:30 (i.e. meeting must finish by 15:30, 930 minutes)
        solver.add(start + duration <= 930)
    
    # Add Janet's busy intervals constraints (none, but loop is kept for uniformity)
    for b in janet_busy.get(day, []):
        solver.add(non_overlap(b[0], b[1]))
    
    # Add Larry's busy intervals constraints.
    for b in larry_busy.get(day, []):
        solver.add(non_overlap(b[0], b[1]))
    
    # Try every possible start time (minute granularity) within work hours
    # Note: Even though the work hours end at 1020, our constraints (and non-overlap) limit the search.
    for t in range(WORK_START, WORK_END - duration + 1):
        solver.push()
        solver.add(start == t)
        if solver.check() == sat:
            meeting_start = t
            meeting_day = day
            found = True
            solver.pop()  # backtrack temporary constraint
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