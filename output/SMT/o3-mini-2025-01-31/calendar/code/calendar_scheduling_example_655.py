from z3 import Solver, Int, Or, sat

# Meeting parameters:
duration = 60  # meeting duration of one hour
start = Int("start")  # meeting start time in minutes from midnight

# Work hours: from 9:00 (540 minutes) to 17:00 (1020 minutes)
WORK_START = 540
WORK_END = 1020

# Busy schedules (times in minutes from midnight)

# Katherine's busy schedule:
# Monday: No busy slots provided
# Tuesday:
#   12:30 to 14:30 -> (750, 870)
#   15:00 to 15:30 -> (900, 930)
#   16:30 to 17:00 -> (990, 1020)
katherine_busy = {
    0: [],
    1: [(750, 870), (900, 930), (990, 1020)]
}

# Andrew's busy schedule:
# Monday:
#   9:00 to 10:00   -> (540, 600)
#   10:30 to 11:00  -> (630, 660)
#   11:30 to 12:30  -> (690, 750)
#   13:30 to 14:00  -> (810, 840)
#   14:30 to 15:00  -> (870, 900)
#   16:00 to 16:30  -> (960, 990)
# Tuesday:
#   9:00 to 10:00   -> (540, 600)
#   10:30 to 11:30  -> (630, 690)
#   12:00 to 14:00  -> (720, 840)
andrew_busy = {
    0: [(540, 600), (630, 660), (690, 750), (810, 840), (870, 900), (960, 990)],
    1: [(540, 600), (630, 690), (720, 840)]
}

# Additional preference:
# Andrew would like to avoid more meetings on Monday.
# Thus, we try to schedule the meeting on Tuesday first if possible; only if no Tuesday slot works, do we try Monday.

# Helper function that ensures the meeting interval [start, start+duration)
# does not overlap with a busy interval [busy_start, busy_end)
def non_overlap(busy_start, busy_end):
    return Or(start + duration <= busy_start, start >= busy_end)

found = False
meeting_day = None  # 0 for Monday, 1 for Tuesday
meeting_start = None

# Try Tuesday first, then Monday based on Andrew's preference.
for day in [1, 0]:
    solver = Solver()
    # Meeting must be within work hours.
    solver.add(start >= WORK_START, start + duration <= WORK_END)
    
    # Add Katherine's busy constraints for the selected day.
    for busy_interval in katherine_busy.get(day, []):
        bs, be = busy_interval
        solver.add(non_overlap(bs, be))
    
    # Add Andrew's busy constraints for the selected day.
    for busy_interval in andrew_busy.get(day, []):
        bs, be = busy_interval
        solver.add(non_overlap(bs, be))
    
    # Iterate minute by minute for possible start times.
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
    start_hour, start_min = divmod(meeting_start, 60)
    end_hour, end_min = divmod(meeting_end, 60)
    day_str = "Monday" if meeting_day == 0 else "Tuesday"
    print(f"A valid meeting time is on {day_str} from {start_hour:02d}:{start_min:02d} to {end_hour:02d}:{end_min:02d}.")
else:
    print("No valid meeting time could be found that meets all constraints.")