from z3 import Solver, Int, Or, Implies, sat

# Meeting parameters:
duration = 30  # meeting duration in minutes (half an hour)
start = Int("start")  # meeting start time (in minutes from midnight)
day = Int("day")      # day: 0 for Monday, 1 for Tuesday

# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
WORK_START = 540
WORK_END = 1020

solver = Solver()
solver.add(start >= WORK_START, start + duration <= WORK_END)
solver.add(Or(day == 0, day == 1))

# Busy schedules in minutes from midnight:

# James's busy schedule:
# Monday:
#   9:00 to 9:30   -> (540, 570)
#   11:30 to 12:00 -> (690, 720)
#   14:00 to 14:30 -> (840, 870)
#   15:30 to 16:00 -> (930, 960)
#   16:30 to 17:00 -> (990, 1020)
james_monday_busy = [(540, 570), (690, 720), (840, 870), (930, 960), (990, 1020)]
# Tuesday:
#   11:30 to 12:00 -> (690, 720)
#   14:00 to 14:30 -> (840, 870)
#   16:00 to 16:30 -> (960, 990)
james_tuesday_busy = [(690, 720), (840, 870), (960, 990)]

# Frank's busy schedule:
# Monday:
#   9:00 to 9:30   -> (540, 570)
#   10:00 to 17:00  -> (600, 1020)
frank_monday_busy = [(540, 570), (600, 1020)]
# Tuesday:
#   9:30 to 10:30  -> (570, 630)
#   11:30 to 12:30 -> (690, 750)
#   13:30 to 14:30 -> (810, 870)
#   15:00 to 15:30 -> (900, 930)
#   16:00 to 17:00 -> (960, 1020)
frank_tuesday_busy = [(570, 630), (690, 750), (810, 870), (900, 930), (960, 1020)]

# Helper function to ensure the meeting interval [start, start+duration) does not overlap a busy interval.
def non_overlap(busy_start, busy_end):
    return Or(start + duration <= busy_start, start >= busy_end)

# Add James's busy schedule constraints:
for b_start, b_end in james_monday_busy:
    solver.add(Implies(day == 0, non_overlap(b_start, b_end)))
for b_start, b_end in james_tuesday_busy:
    solver.add(Implies(day == 1, non_overlap(b_start, b_end)))

# Add Frank's busy schedule constraints:
for b_start, b_end in frank_monday_busy:
    solver.add(Implies(day == 0, non_overlap(b_start, b_end)))
for b_start, b_end in frank_tuesday_busy:
    solver.add(Implies(day == 1, non_overlap(b_start, b_end)))

# Preference: Frank would rather not meet on Tuesday.
# We enforce the preference by attempting to find a Monday solution before trying Tuesday.
# (We do not add a hard constraint against Tuesday because we only try Tuesday if no Monday solution exists.)

# Try to find a Monday meeting first.
found = False
meeting_start = None
meeting_day = None

# Try Monday (day == 0)
for t in range(WORK_START, WORK_END - duration + 1):
    solver.push()
    solver.add(start == t, day == 0)
    if solver.check() == sat:
        model = solver.model()
        meeting_start = model[start].as_long()
        meeting_day = model[day].as_long()  # should be 0 for Monday
        found = True
        solver.pop()
        break
    solver.pop()

# If no valid Monday slot is found, try Tuesday.
if not found:
    for t in range(WORK_START, WORK_END - duration + 1):
        solver.push()
        solver.add(start == t, day == 1)
        if solver.check() == sat:
            model = solver.model()
            meeting_start = model[start].as_long()
            meeting_day = model[day].as_long()  # should be 1 for Tuesday
            found = True
            solver.pop()
            break
        solver.pop()

if found:
    meeting_end = meeting_start + duration
    start_hour, start_min = divmod(meeting_start, 60)
    end_hour, end_min = divmod(meeting_end, 60)
    day_str = "Monday" if meeting_day == 0 else "Tuesday"
    print(f"A valid meeting time is on {day_str} from {start_hour:02d}:{start_min:02d} to {end_hour:02d}:{end_min:02d}.")
else:
    print("No valid meeting time could be found.")