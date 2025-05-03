from z3 import Solver, Int, Or, sat

# Meeting parameters:
duration = 60  # meeting duration is 1 hour (60 minutes)
start = Int("start")  # meeting start time, in minutes from midnight

# Work day limits: 9:00 (540 minutes) to 17:00 (1020 minutes)
WORK_START = 540
WORK_END = 1020

# Busy schedules (times in minutes from midnight):

# Sean's busy schedule:
# Monday:
#   9:30 to 10:00  -> (570, 600)
#   11:00 to 12:00 -> (660, 720)
#   12:30 to 13:30 -> (750, 810)
#   14:00 to 15:00 -> (840, 900)
#   15:30 to 16:00 -> (930, 960)
#   16:30 to 17:00 -> (990, 1020)
# Tuesday:
#   10:00 to 10:30 -> (600, 630)
#   11:00 to 11:30 -> (660, 690)
#   13:30 to 14:00 -> (810, 840)
#   15:00 to 15:30 -> (900, 930)
#   16:00 to 16:30 -> (960, 990)
sean_busy = {
    0: [(570, 600), (660, 720), (750, 810), (840, 900), (930, 960), (990, 1020)],
    1: [(600, 630), (660, 690), (810, 840), (900, 930), (960, 990)]
}

# Carol's busy schedule:
# Monday:
#   9:00 to 12:30 -> (540, 750)
#   13:00 to 17:00 -> (780, 1020)
# Tuesday:
#   9:00 to 9:30   -> (540, 570)
#   11:00 to 11:30 -> (660, 690)
#   12:30 to 14:30 -> (750, 870)
#   15:30 to 17:00 -> (930, 1020)
carol_busy = {
    0: [(540, 750), (780, 1020)],
    1: [(540, 570), (660, 690), (750, 870), (930, 1020)]
}

# Helper function: checks that the meeting interval [start, start+duration)
# does not overlap with a busy interval [busy_start, busy_end)
def non_overlap(busy_start, busy_end):
    return Or(start + duration <= busy_start, start >= busy_end)

found = False
meeting_day = None   # 0 = Monday, 1 = Tuesday
meeting_start = None

# We want the earliest availability.
# Check Monday first (day 0), then Tuesday (day 1) if needed.
for day_val in [0, 1]:
    solver = Solver()
    # Constraint: meeting must happen within work hours.
    solver.add(start >= WORK_START, start + duration <= WORK_END)
    
    # Add Sean's busy constraints for the day.
    for (busy_start, busy_end) in sean_busy.get(day_val, []):
        solver.add(non_overlap(busy_start, busy_end))
    
    # Add Carol's busy constraints for the day.
    for (busy_start, busy_end) in carol_busy.get(day_val, []):
        solver.add(non_overlap(busy_start, busy_end))
    
    # Iterate through possible start times (in minutes) from WORK_START to latest start time.
    for t in range(WORK_START, WORK_END - duration + 1):
        solver.push()  # Save solver state
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