from z3 import Solver, Int, Or, Implies, sat

# Meeting parameters:
duration = 60  # meeting duration: 60 minutes (1 hour)
start = Int("start")  # meeting start time in minutes from midnight
day = Int("day")      # 0 for Monday, 1 for Tuesday

# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
WORK_START = 540
WORK_END = 1020

solver = Solver()
solver.add(start >= WORK_START, start + duration <= WORK_END)
solver.add(Or(day == 0, day == 1))

# Samantha's busy schedule (in minutes from midnight):
# Monday: no busy times.
# Tuesday:
#   12:00 to 12:30 -> (720, 750)
#   16:00 to 16:30 -> (960, 990)
samantha_tuesday_busy = [(720, 750), (960, 990)]

# Joyce's busy schedule (in minutes from midnight):
# Monday:
#   10:00 to 11:00 -> (600, 660)
#   11:30 to 12:30 -> (690, 750)
#   13:00 to 16:00 -> (780, 960)
#   16:30 to 17:00 -> (990, 1020)
joyce_monday_busy = [(600, 660), (690, 750), (780, 960), (990, 1020)]
# Tuesday:
#   9:00 to 11:00   -> (540, 660)
#   11:30 to 17:00  -> (690, 1020)
joyce_tuesday_busy = [(540, 660), (690, 1020)]

# Helper function: meeting [start, start+duration) must not overlap busy interval [busy_start, busy_end)
def non_overlap(busy_start, busy_end):
    return Or(start + duration <= busy_start, start >= busy_end)

# Add Samantha's busy constraints:
# For Monday, Samantha has no busy times.
for b_start, b_end in samantha_tuesday_busy:
    solver.add(Implies(day == 1, non_overlap(b_start, b_end)))

# Add Joyce's busy constraints:
for b_start, b_end in joyce_monday_busy:
    solver.add(Implies(day == 0, non_overlap(b_start, b_end)))
for b_start, b_end in joyce_tuesday_busy:
    solver.add(Implies(day == 1, non_overlap(b_start, b_end)))

# Try to find a valid meeting time:
found = False
meeting_start = None
meeting_day = None

# Check every possible start time in minute increments within work hours.
for t in range(WORK_START, WORK_END - duration + 1):
    solver.push()
    solver.add(start == t)
    if solver.check() == sat:
        model = solver.model()
        meeting_start = model[start].as_long()
        meeting_day = model[day].as_long()  # 0: Monday, 1: Tuesday
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