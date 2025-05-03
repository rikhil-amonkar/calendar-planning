from z3 import Solver, Int, Or, sat

# Meeting parameters:
duration = 30  # meeting duration in minutes (half an hour)
start = Int("start")  # meeting start time in minutes from midnight

# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
WORK_START = 540
WORK_END = 1020

# Busy schedules (times in minutes from midnight)

# Benjamin's busy schedule:
# Monday:
#   15:30 to 16:00 -> (930, 960)
# Tuesday:
#   14:30 to 15:00 -> (870, 900)
benjamin_busy = {
    0: [(930, 960)],
    1: [(870, 900)]
}

# Mark's busy schedule:
# Monday:
#   9:00 to 10:00 -> (540, 600)
#   12:00 to 13:00 -> (720, 780)
#   13:30 to 14:30 -> (810, 870)
# Tuesday:
#   9:00 to 14:00 -> (540, 840)
#   15:00 to 17:00 -> (900, 1020)
mark_busy = {
    0: [(540, 600), (720, 780), (810, 870)],
    1: [(540, 840), (900, 1020)]
}

# Additional constraints:
# - Benjamin cannot meet on Monday.
#   Thus, the meeting day must be Tuesday.
    
# Helper function to ensure that the meeting interval [start, start+duration)
# does not overlap with a given busy interval [busy_start, busy_end).
def non_overlap(busy_start, busy_end):
    return Or(start + duration <= busy_start, start >= busy_end)

found = False
meeting_day = None   # 0 for Monday, 1 for Tuesday
meeting_start = None

# Try scheduling on Monday (day 0) and Tuesday (day 1)
# Given constraints, Benjamin cannot meet on Monday, so we expect a Tuesday meeting.
for day in [0, 1]:
    solver = Solver()
    # Constrain meeting to be within work hours.
    solver.add(start >= WORK_START, start + duration <= WORK_END)
    
    # Day-specific participant constraints:
    if day == 0:
        # Benjamin does not want to meet on Monday.
        solver.add(False)
    # (No extra constraint for Tuesday apart from busy times)
    
    # Add Benjamin's busy intervals for the day.
    for b_start, b_end in benjamin_busy.get(day, []):
        solver.add(non_overlap(b_start, b_end))
        
    # Add Mark's busy intervals for the day.
    for b_start, b_end in mark_busy.get(day, []):
        solver.add(non_overlap(b_start, b_end))
    
    # Iterate over possible start times (minute granularity)
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
    # Convert minutes to HH:MM format:
    start_hr, start_min = divmod(meeting_start, 60)
    end_hr, end_min = divmod(meeting_end, 60)
    day_str = "Monday" if meeting_day == 0 else "Tuesday"
    print(f"A valid meeting time is on {day_str} from {start_hr:02d}:{start_min:02d} to {end_hr:02d}:{end_min:02d}.")
else:
    print("No valid meeting time could be found that meets all constraints.")