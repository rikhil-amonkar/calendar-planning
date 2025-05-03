from z3 import Solver, Int, Or, sat

# Meeting parameters:
duration = 30  # meeting duration is 30 minutes
start = Int("start")  # meeting start time, in minutes from midnight

# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
WORK_START = 540
WORK_END = 1020

# Busy schedules in minutes from midnight:

# Benjamin's busy schedule:
# Monday:
#   9:30-10:00 -> (570,600)
#   14:00-14:30 -> (840,870)
#   15:30-16:00 -> (930,960)
# Tuesday:
#   9:30-11:00 -> (570,660)
benjamin_busy = {
    0: [(570, 600), (840, 870), (930, 960)],
    1: [(570, 660)]
}

# Joe's busy schedule:
# Monday:
#   10:00-10:30 -> (600,630)
#   12:00-13:00 -> (720,780)
#   14:30-15:00 -> (870,900)
#   16:00-17:00 -> (960,1020)
# Tuesday:
#   9:00-9:30 -> (540,570)
#   10:00-12:00 -> (600,720)
#   13:00-14:30 -> (780,870)
#   15:30-16:30 -> (930,990)
joe_busy = {
    0: [(600, 630), (720, 780), (870, 900), (960, 1020)],
    1: [(540, 570), (600, 720), (780, 870), (930, 990)]
}

# Helper function: returns a constraint that ensures the meeting interval [start, start+duration)
# does not overlap with a busy interval [busy_start, busy_end)
def non_overlap(busy_start, busy_end):
    return Or(start + duration <= busy_start, start >= busy_end)

found = False
meeting_day = None  # 0 for Monday, 1 for Tuesday
meeting_start = None

# The group wants the earliest availability.
# Try Monday first (day=0), then Tuesday (day=1) if needed.
for day_val in [0, 1]:
    solver = Solver()
    # Meeting must be within work hours.
    solver.add(start >= WORK_START, start + duration <= WORK_END)
    
    # Add Benjamin's busy constraints for the day.
    for (busy_start, busy_end) in benjamin_busy.get(day_val, []):
        solver.add(non_overlap(busy_start, busy_end))
    
    # Add Joe's busy constraints for the day.
    for (busy_start, busy_end) in joe_busy.get(day_val, []):
        solver.add(non_overlap(busy_start, busy_end))
    
    # Check each possible starting minute of the day (earlier minutes first)
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