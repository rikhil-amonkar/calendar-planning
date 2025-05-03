from z3 import Solver, Int, Or, sat

# Meeting parameters:
duration = 30  # meeting duration is 30 minutes
start = Int("start")  # meeting start time, in minutes from midnight

# Work hours: from 9:00 (540 minutes) to 17:00 (1020 minutes)
WORK_START = 540
WORK_END = 1020

# Busy schedules (times given in minutes from midnight):

# Samuel's busy schedule:
# Monday:
#   10:30 to 11:30 -> (630, 690)
#   13:30 to 14:00 -> (810, 840)
#   14:30 to 15:00 -> (870, 900)
#   16:00 to 17:00 -> (960, 1020)
# Tuesday:
#   9:00 to 9:30   -> (540, 570)
#   10:30 to 11:00 -> (630, 660)
#   12:00 to 13:00 -> (720, 780)
#   14:00 to 14:30 -> (840, 870)
#   15:30 to 16:00 -> (930, 960)
samuel_busy = {
    0: [(630, 690), (810, 840), (870, 900), (960, 1020)],
    1: [(540, 570), (630, 660), (720, 780), (840, 870), (930, 960)]
}

# Pamela's busy schedule:
# Monday:
#   9:00 to 14:30 -> (540, 870)
#   15:00 to 17:00 -> (900, 1020)
# Tuesday:
#   9:00 to 11:00  -> (540, 660)
#   11:30 to 17:00 -> (690, 1020)
pamela_busy = {
    0: [(540, 870), (900, 1020)],
    1: [(540, 660), (690, 1020)]
}

# Helper function: Ensures that the meeting interval [start, start+duration)
# does not overlap with a busy interval [busy_start, busy_end)
def non_overlap(busy_start, busy_end):
    return Or(start + duration <= busy_start, start >= busy_end)

found = False
meeting_day = None  # 0 for Monday, 1 for Tuesday
meeting_start = None

# We want the earliest available time.
# Try Monday first, then Tuesday.
for day in [0, 1]:
    solver = Solver()
    # The meeting must be within work hours.
    solver.add(start >= WORK_START, start + duration <= WORK_END)
    
    # Add Samuel's busy constraints for the selected day.
    for (busy_start, busy_end) in samuel_busy.get(day, []):
        solver.add(non_overlap(busy_start, busy_end))
    
    # Add Pamela's busy constraints for the selected day.
    for (busy_start, busy_end) in pamela_busy.get(day, []):
        solver.add(non_overlap(busy_start, busy_end))
    
    # Iterate over possible start times minute by minute.
    for t in range(WORK_START, WORK_END - duration + 1):
        solver.push()  # save solver state
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
    start_hour, start_min = divmod(meeting_start, 60)
    end_hour, end_min = divmod(meeting_end, 60)
    day_str = "Monday" if meeting_day == 0 else "Tuesday"
    print(f"A valid meeting time is on {day_str} from {start_hour:02d}:{start_min:02d} to {end_hour:02d}:{end_min:02d}.")
else:
    print("No valid meeting time could be found that meets all constraints.")