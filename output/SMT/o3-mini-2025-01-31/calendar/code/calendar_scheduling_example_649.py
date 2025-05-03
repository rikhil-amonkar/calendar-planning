from z3 import Solver, Int, Or, sat

# Meeting parameters:
duration = 60  # meeting duration is 1 hour (60 minutes)
start = Int("start")  # meeting start time in minutes from midnight

# Work day limits: 9:00 (540 minutes) to 17:00 (1020 minutes)
WORK_START = 540
WORK_END = 1020

# Busy schedules (in minutes from midnight):

# Jose's busy schedule:
# Monday:
#   9:00-9:30  -> (540, 570)
#   15:30-16:00 -> (930, 960)
# Tuesday:
#   10:00-10:30 -> (600, 630)
#   11:30-12:00 -> (690, 720)
#   15:00-15:30 -> (900, 930)
#   16:00-16:30 -> (960, 990)
jose_busy = {
    0: [(540, 570), (930, 960)],
    1: [(600, 630), (690, 720), (900, 930), (960, 990)]
}

# Bryan's busy schedule:
# Monday:
#   9:30-10:30  -> (570, 630)
#   11:00-12:00 -> (660, 720)
#   12:30-13:00 -> (750, 780)
#   13:30-14:30 -> (810, 870)
#   15:30-16:00 -> (930, 960)
# Tuesday:
#   9:00-10:00   -> (540, 600)
#   10:30-11:00  -> (630, 660)
#   11:30-12:00  -> (690, 720)
#   12:30-13:00  -> (750, 780)
#   13:30-14:00  -> (810, 840)
#   14:30-15:00  -> (870, 900)
#   16:00-16:30  -> (960, 990)
bryan_busy = {
    0: [(570, 630), (660, 720), (750, 780), (810, 870), (930, 960)],
    1: [(540, 600), (630, 660), (690, 720), (750, 780), (810, 840), (870, 900), (960, 990)]
}

# Helper function: the meeting interval [start, start+duration)
# must not overlap with a busy interval [busy_start, busy_end).
def non_overlap(busy_start, busy_end):
    return Or(start + duration <= busy_start, start >= busy_end)

found = False
meeting_day = None  # 0 = Monday, 1 = Tuesday
meeting_start = None

# The group wants the meeting at their earliest availability.
# Try Monday (day 0) first, then Tuesday (day 1) if needed.
for day_val in [0, 1]:
    solver = Solver()
    # Meeting must be within work hours.
    solver.add(start >= WORK_START, start + duration <= WORK_END)
    
    # Add Jose's busy constraints for the day.
    for (busy_start, busy_end) in jose_busy.get(day_val, []):
        solver.add(non_overlap(busy_start, busy_end))
    
    # Add Bryan's busy constraints for the day.
    for (busy_start, busy_end) in bryan_busy.get(day_val, []):
        solver.add(non_overlap(busy_start, busy_end))
    
    # Check possible start times in minute increments (earliest first).
    for t in range(WORK_START, WORK_END - duration + 1):
        solver.push()
        solver.add(start == t)
        if solver.check() == sat:
            meeting_start = t
            meeting_day = day_val
            found = True
            solver.pop()
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
    print("No valid meeting time could be found.")