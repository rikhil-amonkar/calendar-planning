from z3 import Solver, Int, Or, sat

# Meeting parameters:
duration = 60  # meeting length of 1 hour (60 minutes)
start = Int("start")  # meeting start time (in minutes from midnight)

# Work day limits: 9:00 (540 minutes) to 17:00 (1020 minutes)
WORK_START = 540
WORK_END = 1020

# Busy schedules (times in minutes from midnight):

# Arthur's busy schedule:
# Monday:
#   14:00 to 14:30 -> (840, 870)
# Tuesday:
#   12:00 to 13:00 -> (720, 780)
#   15:30 to 16:00 -> (930, 960)
arthur_busy = {
    0: [(840, 870)],
    1: [(720, 780), (930, 960)]
}

# Thomas's busy schedule:
# Monday:
#   10:00 to 12:00 -> (600, 720)
#   12:30 to 13:00 -> (750, 780)
#   13:30 to 14:00 -> (810, 840)
#   14:30 to 17:00 -> (870, 1020)
# Tuesday:
#   10:00 to 12:00 -> (600, 720)
#   13:00 to 15:00 -> (780, 900)
#   15:30 to 17:00 -> (930, 1020)
thomas_busy = {
    0: [(600, 720), (750, 780), (810, 840), (870, 1020)],
    1: [(600, 720), (780, 900), (930, 1020)]
}

# Arthur has specified that he does NOT want to meet on Tuesday.
# Thus we enforce that the meeting must be scheduled on Monday (day 0).

# Helper function: ensures that the meeting interval [start, start+duration)
# does not overlap with a busy interval [busy_start, busy_end)
def non_overlap(busy_start, busy_end):
    return Or(start + duration <= busy_start, start >= busy_end)

found = False
meeting_day = None   # 0 = Monday, 1 = Tuesday
meeting_start = None

# Since Arthur does not want Tuesday, we only consider Monday (day 0):
for day_val in [0]:
    solver = Solver()
    # Constraint: meeting must occur within work hours.
    solver.add(start >= WORK_START, start + duration <= WORK_END)
    
    # Add Arthur's busy constraints for the day.
    for (busy_start, busy_end) in arthur_busy.get(day_val, []):
        solver.add(non_overlap(busy_start, busy_end))
    
    # Add Thomas's busy constraints for the day.
    for (busy_start, busy_end) in thomas_busy.get(day_val, []):
        solver.add(non_overlap(busy_start, busy_end))
    
    # Try possible meeting start times (minute by minute) from WORK_START.
    for t in range(WORK_START, WORK_END - duration + 1):
        solver.push()  # Save state
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
    print("No valid meeting time could be found that meets all constraints.")