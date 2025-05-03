from z3 import Solver, Int, Or, sat

# Meeting parameters:
duration = 30  # meeting duration in minutes (half an hour)
start = Int("start")  # meeting start time in minutes from midnight

# Work hours: from 9:00 (540 minutes) to 17:00 (1020 minutes)
WORK_START = 540
WORK_END = 1020

# Busy schedules (times expressed in minutes from midnight):

# Willie's busy schedule:
# Monday: 15:30 to 16:00 -> (930, 960)
# Tuesday: 12:00 to 12:30 -> (720, 750)
willie_busy = {
    0: [(930, 960)],
    1: [(720, 750)]
}

# Mark's busy schedule:
# Monday:
#   9:30 to 10:00 -> (570, 600)
#   11:00 to 13:00 -> (660, 780)
#   13:30 to 14:00 -> (810, 840)
#   15:00 to 17:00 -> (900, 1020)
# Tuesday:
#   9:00 to 11:00 -> (540, 660)
#   11:30 to 12:00 -> (690, 720)
#   12:30 to 15:30 -> (750, 930)
#   16:00 to 16:30 -> (960, 990)
mark_busy = {
    0: [(570, 600), (660, 780), (810, 840), (900, 1020)],
    1: [(540, 660), (690, 720), (750, 930), (960, 990)]
}

# Additional requirement:
# "The group would like to meet at their earliest availability."
# We will search Monday first, then Tuesday, and within each day we iterate from WORK_START upwards.
# Monday will correspond to day = 0 and Tuesday to day = 1.

# Helper function:
# Ensure that the meeting interval [start, start + duration) does not overlap with a busy interval [busy_start, busy_end)
def non_overlap(busy_start, busy_end):
    return Or(start + duration <= busy_start, start >= busy_end)

found = False
meeting_day = None   # 0 for Monday, 1 for Tuesday
meeting_start = None

# We'll try Monday first (day 0) then Tuesday (day 1) to ensure earliest availability
for day in [0, 1]:
    solver = Solver()
    # The meeting must lie within the work hours.
    solver.add(start >= WORK_START, start + duration <= WORK_END)
    
    # Add constraints for Willie's busy schedule on the day.
    for b_start, b_end in willie_busy.get(day, []):
        solver.add(non_overlap(b_start, b_end))
    
    # Add constraints for Mark's busy schedule on the day.
    for b_start, b_end in mark_busy.get(day, []):
        solver.add(non_overlap(b_start, b_end))
    
    # Enumerate possible start times (minute-by-minute) for this day.
    for t in range(WORK_START, WORK_END - duration + 1):
        solver.push()
        solver.add(start == t)
        if solver.check() == sat:
            meeting_start = t
            meeting_day = day
            found = True
            solver.pop()  # remove the equality constraint before breaking out
            break
        solver.pop()
    
    if found:
        break

if found:
    meeting_end = meeting_start + duration
    sh, sm = divmod(meeting_start, 60)
    eh, em = divmod(meeting_end, 60)
    day_str = "Monday" if meeting_day == 0 else "Tuesday"
    print(f"A valid meeting time is on {day_str} from {sh:02d}:{sm:02d} to {eh:02d}:{em:02d}.")
else:
    print("No valid meeting time could be found that meets all constraints.")