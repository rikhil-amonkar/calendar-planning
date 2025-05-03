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

# Participant preferences:
# Russell cannot meet on Tuesday, so meeting must be on Monday.
solver.add(day == 0)
# Amy would rather not meet on Monday after 13:30.
# For Monday (day == 0), the meeting must end by 13:30 (810 minutes).
solver.add(Implies(day == 0, start + duration <= 810))

# Busy schedules (times in minutes from midnight):

# Russell's busy times on Monday:
#   11:00 to 12:30 -> (660, 750)
russell_monday_busy = [
    (660, 750)
]
# (Tuesday busy times are not relevant since meeting must be on Monday.)

# Amy's busy times on Monday:
#   9:00 to 9:30   -> (540, 570)
#   10:30 to 11:30 -> (630, 690)
#   12:30 to 13:00 -> (750, 780)
amy_monday_busy = [
    (540, 570),
    (630, 690),
    (750, 780)
]
# (Tuesday busy times are not relevant since meeting is on Monday.)

# Helper function: meeting interval [start, start+duration) must not overlap busy interval [busy_start, busy_end)
def non_overlap(busy_start, busy_end):
    return Or(start + duration <= busy_start, start >= busy_end)

# Add Russell's busy constraints on Monday:
for b_start, b_end in russell_monday_busy:
    solver.add(Implies(day == 0, non_overlap(b_start, b_end)))

# Add Amy's busy constraints on Monday:
for b_start, b_end in amy_monday_busy:
    solver.add(Implies(day == 0, non_overlap(b_start, b_end)))

# Search for a valid meeting time by iterating minute-by-minute within work hours.
found = False
meeting_start = None
meeting_day = None

for t in range(WORK_START, WORK_END - duration + 1):
    solver.push()
    solver.add(start == t)
    if solver.check() == sat:
        model = solver.model()
        meeting_start = model[start].as_long()
        meeting_day = model[day].as_long()  # 0: Monday, 1: Tuesday (but will be 0 here)
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