from z3 import Solver, Int, Or, Implies, sat

# Meeting parameters:
duration = 30  # meeting duration is 30 minutes
start = Int("start")  # meeting start time in minutes from midnight
day = Int("day")      # day: 0 for Monday, 1 for Tuesday

# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
WORK_START = 540
WORK_END = 1020

solver = Solver()
solver.add(start >= WORK_START, start + duration <= WORK_END)
solver.add(Or(day == 0, day == 1))

# Constraint: Margaret does not want to meet on Monday,
# so the meeting must be scheduled on Tuesday (day == 1).
solver.add(day == 1)

# Additional preference from Margaret: on Tuesday the meeting must be before 14:30.
# We interpret this as the meeting ending by 14:30 (i.e., 870 minutes).
solver.add(start + duration <= 870)

# Busy schedules in minutes since midnight:
# Margaret's busy times:
#   Tuesday: 12:00 to 12:30 -> (720, 750)
margaret_tuesday_busy = [(720, 750)]

# Alexis's busy times:
#   Tuesday:
#     9:00 to 9:30   -> (540, 570),
#     10:00 to 10:30 -> (600, 630),
#     14:00 to 16:30 -> (840, 990)
alexis_tuesday_busy = [(540, 570), (600, 630), (840, 990)]

# Helper function: the meeting [start, start+duration) must not overlap a busy interval [busy_start, busy_end)
def non_overlap(busy_start, busy_end):
    return Or(start + duration <= busy_start, start >= busy_end)

# Add Margaret's busy schedule constraints for Tuesday:
for b_start, b_end in margaret_tuesday_busy:
    solver.add(Implies(day == 1, non_overlap(b_start, b_end)))

# Add Alexis's busy schedule constraints for Tuesday:
for b_start, b_end in alexis_tuesday_busy:
    solver.add(Implies(day == 1, non_overlap(b_start, b_end)))

found = False
meeting_start = None
meeting_day = None

# Iterate over possible start times (minute-by-minute)
for t in range(WORK_START, WORK_END - duration + 1):
    solver.push()
    solver.add(start == t)
    if solver.check() == sat:
        model = solver.model()
        meeting_start = model[start].as_long()
        meeting_day = model[day].as_long()  # This will be 1 (Tuesday)
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