from z3 import Solver, Int, Or, sat

# Meeting parameters:
duration = 30  # meeting duration in minutes
start = Int("start")  # meeting start time in minutes after midnight

# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
WORK_START = 540
WORK_END = 1020

# Busy schedules in minutes from midnight:

# Roy's busy schedule:
# Monday:
#   10:00 to 10:30 -> (600, 630)
#   12:00 to 13:30 -> (720, 810)
#   14:30 to 15:30 -> (870, 930)
# Tuesday:
#   9:30 to 10:00   -> (570, 600)
#   10:30 to 12:00  -> (630, 720)
#   12:30 to 13:00  -> (750, 780)
#   13:30 to 14:30  -> (810, 870)
#   15:30 to 16:00  -> (930, 960)
roy_busy = {
    0: [(600, 630), (720, 810), (870, 930)],
    1: [(570, 600), (630, 720), (750, 780), (810, 870), (930, 960)]
}

# Nancy's busy schedule:
# Monday:
#   9:30 to 10:00   -> (570, 600)
#   14:00 to 14:30  -> (840, 870)
#   15:00 to 15:30  -> (900, 930)
#   16:00 to 17:00  -> (960, 1020)
# Tuesday:
#   10:00 to 13:00  -> (600, 780)
#   14:00 to 14:30  -> (840, 870)
#   15:00 to 17:00  -> (900, 1020)
nancy_busy = {
    0: [(570, 600), (840, 870), (900, 930), (960, 1020)],
    1: [(600, 780), (840, 870), (900, 1020)]
}

# Additional constraints:
# Roy cannot meet on Monday.
# Nancy does not want to meet on Tuesday before 13:30 (i.e., before 810 minutes).
# We'll encode these preferences as hard constraints.

# Helper function to ensure that the meeting interval [start, start+duration)
# does not overlap with a busy interval [busy_start, busy_end)
def non_overlap(busy_start, busy_end):
    return Or(start + duration <= busy_start, start >= busy_end)

found = False
meeting_day = None  # 0 for Monday, 1 for Tuesday
meeting_start = None

# We iterate over days. To respect the constraints:
#   - Roy cannot meet on Monday: we force Monday to be unsolvable.
#   - Nancy prefers not to meet on Tuesday before 13:30: add constraint on Tuesday.
for day in [1, 0]:
    solver = Solver()
    
    # Meeting must be within working hours.
    solver.add(start >= WORK_START, start + duration <= WORK_END)
    
    # If day is Monday (0), Roy cannot attend.
    if day == 0:
        # Force Monday to be unsolvable for Roy.
        solver.add(False)
    
    # If day is Tuesday (1), Nancy does not want meetings before 13:30.
    if day == 1:
        solver.add(start >= 810)  # 13:30 in minutes
    
    # Add Roy's busy constraints for this day.
    for (busy_start, busy_end) in roy_busy.get(day, []):
        solver.add(non_overlap(busy_start, busy_end))
    
    # Add Nancy's busy constraints for this day.
    for (busy_start, busy_end) in nancy_busy.get(day, []):
        solver.add(non_overlap(busy_start, busy_end))
    
    # Iterate through possible start times minute-by-minute.
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