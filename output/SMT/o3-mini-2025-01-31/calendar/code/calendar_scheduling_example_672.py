from z3 import Solver, Int, Or, sat

# Meeting parameters:
duration = 30  # meeting duration in minutes (half an hour)
start = Int("start")  # meeting start time in minutes from midnight

# Work hours: from 9:00 (540 minutes) to 17:00 (1020 minutes)
WORK_START = 540
WORK_END = 1020

# Busy schedules (times expressed in minutes from midnight):

# Harold's busy schedule:
# Monday (day 0):
#   9:30 to 10:00  -> (570, 600)
#   12:00 to 12:30 -> (720, 750)
#   13:30 to 14:00 -> (810, 840)
#   14:30 to 15:30 -> (870, 930)
# Tuesday (day 1):
#   10:30 to 11:00 -> (630, 660)
#   11:30 to 12:00 -> (690, 720)
#   12:30 to 13:00 -> (750, 780)
#   14:30 to 15:00 -> (870, 900)
#   15:30 to 16:00 -> (930, 960)
harold_busy = {
    0: [(570, 600), (720, 750), (810, 840), (870, 930)],
    1: [(630, 660), (690, 720), (750, 780), (870, 900), (930, 960)]
}

# Donna's busy schedule:
# Monday (day 0):
#   9:00 to 11:00  -> (540, 660)
#   12:30 to 16:00 -> (750, 960)
# Tuesday (day 1):
#   9:00 to 10:30  -> (540, 630)
#   12:00 to 17:00 -> (720, 1020)
donna_busy = {
    0: [(540, 660), (750, 960)],
    1: [(540, 630), (720, 1020)]
}

# Additional preferences:
# - Harold does NOT want to meet on Monday after 12:30.
#   => If the meeting is on Monday (day 0), it must finish by 12:30, meaning start + duration <= 750.
# - Donna would like to avoid more meetings on Tuesday.
#   => We will prioritize Monday over Tuesday by trying Monday first.

# Helper function to enforce that meeting interval [start, start+duration)
# does not overlap with a busy interval [busy_start, busy_end)
def non_overlap(busy_start, busy_end):
    # Either the meeting ends before the busy interval starts,
    # or it starts after the busy interval finishes.
    return Or(start + duration <= busy_start, start >= busy_end)

found = False
meeting_day = None  # 0 for Monday, 1 for Tuesday
meeting_start = None

# Try scheduling on Monday (day 0) first, then Tuesday (day 1) if necessary.
for day in [0, 1]:
    solver = Solver()
    # Ensure meeting is fully within work hours:
    solver.add(start >= WORK_START, start + duration <= WORK_END)
    
    # Apply Harold's preference for Monday: meeting must finish by 12:30 on Monday.
    if day == 0:
        solver.add(start + duration <= 750)
    
    # Add busy intervals for Harold:
    for busy_interval in harold_busy.get(day, []):
        solver.add(non_overlap(busy_interval[0], busy_interval[1]))
    
    # Add busy intervals for Donna:
    for busy_interval in donna_busy.get(day, []):
        solver.add(non_overlap(busy_interval[0], busy_interval[1]))
    
    # Try every possible start time within work hours (minute granularity):
    for t in range(WORK_START, WORK_END - duration + 1):
        solver.push()
        solver.add(start == t)
        if solver.check() == sat:
            meeting_start = t
            meeting_day = day
            found = True
            solver.pop()  # Remove the temporary constraint
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