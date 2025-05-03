from z3 import Solver, Int, Or, sat

# Meeting parameters:
duration = 30  # meeting duration is 30 minutes
start = Int("start")  # meeting start time in minutes from midnight

# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
WORK_START = 540
WORK_END = 1020

# Busy schedules (in minutes from midnight):

# Lisa's busy schedule:
# Monday: 12:30 to 13:00 -> (750, 780)
# Tuesday: 10:00 to 10:30 -> (600, 630)
lisa_busy = {
    0: [(750, 780)],
    1: [(600, 630)]
}

# Janet's busy schedule:
# Monday:
#   9:30 to 10:30 -> (570, 630)
#   11:00 to 11:30 -> (660, 690)
#   12:30 to 14:00 -> (750, 840)
#   14:30 to 15:00 -> (870, 900)
# Tuesday:
#   9:00 to 10:00   -> (540, 600)
#   10:30 to 11:30 -> (630, 690)
#   12:30 to 15:30 -> (750, 930)
#   16:00 to 16:30 -> (960, 990)
janet_busy = {
    0: [(570, 630), (660, 690), (750, 840), (870, 900)],
    1: [(540, 600), (630, 690), (750, 930), (960, 990)]
}

# Additional preferences:
# Lisa would rather not meet on Monday after 15:00.
# We enforce that on Monday (day 0) the meeting must start before 15:00 (i.e., start < 900).
#
# Janet would like to avoid more meetings on Tuesday.
# As a preference, we try Monday (day 0) first. Only if no Monday meeting is found, we try Tuesday.

# Helper function to ensure that a meeting interval [start, start+duration)
# does not overlap with a busy interval [busy_start, busy_end)
def non_overlap(busy_start, busy_end):
    return Or(start + duration <= busy_start, start >= busy_end)

found = False
meeting_day = None  # 0 for Monday, 1 for Tuesday
meeting_start = None

# Try scheduling on Monday first (day 0), then Tuesday (day 1)
for day in [0, 1]:
    solver = Solver()
    
    # Meeting must be within work hours.
    solver.add(start >= WORK_START, start + duration <= WORK_END)
    
    # Apply Lisa's preference if meeting is on Monday:
    if day == 0:
        solver.add(start < 900)  # Meeting must start before 15:00 on Monday.
    
    # Add busy constraints for Lisa.
    for (busy_start, busy_end) in lisa_busy.get(day, []):
        solver.add(non_overlap(busy_start, busy_end))
    
    # Add busy constraints for Janet.
    for (busy_start, busy_end) in janet_busy.get(day, []):
        solver.add(non_overlap(busy_start, busy_end))
    
    # Iterate through possible start times minute by minute.
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