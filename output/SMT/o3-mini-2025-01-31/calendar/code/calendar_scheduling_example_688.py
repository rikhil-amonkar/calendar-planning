from z3 import Solver, Int, Or, sat

# Meeting parameters:
duration = 30  # meeting duration in minutes
start = Int("start")  # meeting start time in minutes from midnight

# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
WORK_START = 540
WORK_END = 1020

# Busy schedules (times in minutes from midnight)

# Edward's busy schedule:
# Monday:
#   13:00 to 13:30 -> (780, 810)
#   14:30 to 15:00 -> (870, 900)
# Tuesday:
#   9:30 to 10:00  -> (570, 600)
#   11:00 to 12:00 -> (660, 720)
#   15:00 to 15:30 -> (900, 930)
edward_busy = {
    0: [(780, 810), (870, 900)],
    1: [(570, 600), (660, 720), (900, 930)]
}

# Angela's busy schedule:
# Monday:
#   9:00 to 9:30   -> (540, 570)
#   10:00 to 10:30 -> (600, 630)
#   11:00 to 12:30 -> (660, 750)
#   13:00 to 15:00 -> (780, 900)
#   15:30 to 16:00 -> (930, 960)
# Tuesday:
#   10:00 to 10:30 -> (600, 630)
#   11:00 to 11:30 -> (660, 690)
#   13:00 to 13:30 -> (780, 810)
#   14:00 to 14:30 -> (840, 870)
#   15:00 to 17:00 -> (900, 1020)
angela_busy = {
    0: [(540, 570), (600, 630), (660, 750), (780, 900), (930, 960)],
    1: [(600, 630), (660, 690), (780, 810), (840, 870), (900, 1020)]
}

# The group would like to meet at their earliest availability.
# This implies we search for a solution on Monday first, then Tuesday, and
# within each day, we try earlier meeting start times first.

# Helper function to ensure that the meeting interval [start, start + duration)
# does not overlap with an existing busy interval [busy_start, busy_end)
def non_overlap(busy_start, busy_end):
    # Either the meeting ends before the busy interval starts, or it starts after the busy interval ends.
    return Or(start + duration <= busy_start, start >= busy_end)

found = False
meeting_day = None  # 0 for Monday, 1 for Tuesday
meeting_start = None

# Attempt scheduling on Monday first (day 0), then Tuesday (day 1)
for day in [0, 1]:
    solver = Solver()
    # Constrain meeting to be within work hours.
    solver.add(start >= WORK_START, start + duration <= WORK_END)
    
    # Add Edward's busy constraints for the day.
    for b_start, b_end in edward_busy.get(day, []):
        solver.add(non_overlap(b_start, b_end))
        
    # Add Angela's busy constraints for the day.
    for b_start, b_end in angela_busy.get(day, []):
        solver.add(non_overlap(b_start, b_end))
    
    # Try possible start times in minute increments starting from WORK_START.
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
    # Convert meeting times (in minutes) to HH:MM format.
    start_hour, start_min = divmod(meeting_start, 60)
    end_hour, end_min = divmod(meeting_end, 60)
    day_str = "Monday" if meeting_day == 0 else "Tuesday"
    print(f"A valid meeting time is on {day_str} from {start_hour:02d}:{start_min:02d} to {end_hour:02d}:{end_min:02d}.")
else:
    print("No valid meeting time could be found that meets all constraints.")