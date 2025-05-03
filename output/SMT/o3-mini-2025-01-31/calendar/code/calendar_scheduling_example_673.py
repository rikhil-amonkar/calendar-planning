from z3 import Solver, Int, Or, sat

# Meeting parameters:
duration = 30  # duration in minutes (half an hour)
start = Int("start")  # meeting start time in minutes from midnight

# Work hours: from 9:00 (540 minutes) to 17:00 (1020 minutes)
WORK_START = 540
WORK_END = 1020

# Busy schedules (times expressed in minutes from midnight):

# James' busy schedule:
# Monday (day 0):
#   9:00 to 10:30 -> (540, 630)
#   11:00 to 11:30 -> (660, 690)
#   13:30 to 14:00 -> (810, 840)
#   15:00 to 16:00 -> (900, 960)
#   16:30 to 17:00 -> (990, 1020)
# Tuesday (day 1):
#   10:00 to 11:30 -> (600, 690)
#   15:00 to 15:30 -> (900, 930)
james_busy = {
    0: [(540, 630), (660, 690), (810, 840), (900, 960), (990, 1020)],
    1: [(600, 690), (900, 930)]
}

# Patricia's busy schedule:
# Monday (day 0):
#   9:30 to 11:00  -> (570, 660)
#   11:30 to 12:30 -> (690, 750)
#   13:00 to 14:00 -> (780, 840)
#   15:00 to 16:30 -> (900, 990)
# Tuesday (day 1):
#   9:00 to 11:00  -> (540, 660)
#   11:30 to 12:30 -> (690, 750)
#   13:00 to 14:30 -> (780, 870)
#   15:00 to 16:30 -> (900, 990)
patricia_busy = {
    0: [(570, 660), (690, 750), (780, 840), (900, 990)],
    1: [(540, 660), (690, 750), (780, 870), (900, 990)]
}

# Additional constraints/preferences:
# - Patricia does not want to meet on Monday.
# - If meeting is on Tuesday, it must not be scheduled before 16:30.
#   Note: 16:30 is 990 minutes from midnight, so on Tuesday we force start >= 990.

# Helper function to ensure that the meeting interval [start, start+duration)
# does not overlap with a given busy interval [busy_start, busy_end).
def non_overlap(busy_start, busy_end):
    return Or(start + duration <= busy_start, start >= busy_end)

found = False
meeting_day = None  # 0 for Monday, 1 for Tuesday
meeting_start = None

# We try possible days. Since Patricia does not want Monday,
# we enforce Monday to be rejected, so only Tuesday (day 1) is expected.
for day in [0, 1]:
    solver = Solver()
    # Ensure meeting is completely within work hours.
    solver.add(start >= WORK_START, start + duration <= WORK_END)
    
    if day == 0:
        # Patricia does not want to meet on Monday.
        solver.add(False)
    elif day == 1:
        # On Tuesday, Patricia prefers not to meet before 16:30 (990 minutes).
        solver.add(start >= 990)
    
    # Add James' busy intervals constraints.
    for b_start, b_end in james_busy.get(day, []):
        solver.add(non_overlap(b_start, b_end))
    
    # Add Patricia's busy intervals constraints.
    for b_start, b_end in patricia_busy.get(day, []):
        solver.add(non_overlap(b_start, b_end))
    
    # Search for a start time (minute granularity)
    for t in range(WORK_START, WORK_END - duration + 1):
        solver.push()
        solver.add(start == t)
        if solver.check() == sat:
            meeting_start = t
            meeting_day = day
            found = True
            solver.pop()  # remove the temporary constraint before breaking
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