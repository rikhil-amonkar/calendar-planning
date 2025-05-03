from z3 import Solver, Int, Or, Implies, sat

# Meeting parameters:
duration = 60  # meeting duration is 60 minutes (1 hour)
start = Int("start")  # meeting start time in minutes from midnight
day = Int("day")      # day: 0 for Monday, 1 for Tuesday

# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
WORK_START = 540
WORK_END = 1020

solver = Solver()
solver.add(start >= WORK_START, start + duration <= WORK_END)
solver.add(Or(day == 0, day == 1))

# Eric's busy schedule in minutes from midnight:
# Monday busy intervals for Eric:
#   9:00 to 12:30 -> (540, 750)
#   13:00 to 15:00 -> (780, 900)
#   16:00 to 17:00 -> (960, 1020)
eric_monday_busy = [
    (540, 750),
    (780, 900),
    (960, 1020)
]

# Tuesday busy intervals for Eric:
#   9:30 to 11:30  -> (570, 690)
#   12:00 to 13:00 -> (720, 780)
#   13:30 to 14:00 -> (810, 840)
#   14:30 to 16:30 -> (870, 990)
eric_tuesday_busy = [
    (570, 690),
    (720, 780),
    (810, 840),
    (870, 990)
]

# Helper function: meeting interval [start, start+duration) should not overlap busy [busy_start, busy_end)
def non_overlap(busy_start, busy_end):
    return Or(start + duration <= busy_start, start >= busy_end)

# Apply Eric's constraints based on the day
for busy_start, busy_end in eric_monday_busy:
    solver.add(Implies(day == 0, non_overlap(busy_start, busy_end)))

for busy_start, busy_end in eric_tuesday_busy:
    solver.add(Implies(day == 1, non_overlap(busy_start, busy_end)))

# Since Judith has no meetings, no additional constraints are needed for her.

# Try to find a valid meeting time by checking minute-by-minute possibilities.
found = False
meeting_start = None
meeting_day = None

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
    s_hour, s_min = divmod(meeting_start, 60)
    e_hour, e_min = divmod(meeting_end, 60)
    day_str = "Monday" if meeting_day == 0 else "Tuesday"
    print(f"A valid meeting time is on {day_str} from {s_hour:02d}:{s_min:02d} to {e_hour:02d}:{e_min:02d}.")
else:
    print("No valid meeting time could be found.")