from z3 import Solver, Int, Or, Implies, sat

# Meeting parameters:
duration = 30  # duration in minutes
start = Int("start")  # meeting start time in minutes from midnight
day = Int("day")      # day: 0 for Monday, 1 for Tuesday

# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
WORK_START = 540
WORK_END = 1020

solver = Solver()
solver.add(start >= WORK_START, start + duration <= WORK_END)
solver.add(Or(day == 0, day == 1))

# Alexis's constraints:
# - Does not want to meet on Monday => meeting must be on Tuesday (day == 1)
# - Does not want Tuesday meetings after 13:30 => meeting must finish by 13:30 (i.e., start + duration <= 810)
solver.add(day == 1)
solver.add(start + duration <= 810)

# Busy schedules (times in minutes from midnight):

# Alexis's busy times:
# Tuesday:
#   10:30 to 11:00 -> (630, 660)
#   12:00 to 13:00 -> (720, 780)
#   14:00 to 15:00 -> (840, 900)
alexis_tuesday_busy = [
    (630, 660),
    (720, 780),
    (840, 900)
]

# Roy's busy times:
# Tuesday:
#   9:00 to 9:30   -> (540, 570)
#   10:00 to 16:00 -> (600, 960)
#   16:30 to 17:00 -> (990, 1020)
roy_tuesday_busy = [
    (540, 570),
    (600, 960),
    (990, 1020)
]

# Helper function: meeting [start, start+duration) must not overlap busy interval [busy_start, busy_end)
def non_overlap(busy_start, busy_end):
    return Or(start + duration <= busy_start, start >= busy_end)

# Add busy constraints for Alexis on Tuesday:
for b_start, b_end in alexis_tuesday_busy:
    solver.add(Implies(day == 1, non_overlap(b_start, b_end)))

# Add busy constraints for Roy on Tuesday:
for b_start, b_end in roy_tuesday_busy:
    solver.add(Implies(day == 1, non_overlap(b_start, b_end)))

# Search for a valid meeting time minute-by-minute.
found = False
meeting_start = None
meeting_day = None

for t in range(WORK_START, WORK_END - duration + 1):
    solver.push()
    solver.add(start == t)
    if solver.check() == sat:
        model = solver.model()
        meeting_start = model[start].as_long()
        meeting_day = model[day].as_long()  # will be 1 (Tuesday)
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