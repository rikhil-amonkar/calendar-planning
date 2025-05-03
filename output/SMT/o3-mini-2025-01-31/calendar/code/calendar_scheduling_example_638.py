from z3 import Solver, Int, Or, Implies, sat

# Meeting parameters:
duration = 30  # meeting duration in minutes
start = Int("start")  # meeting start time in minutes from midnight
day = Int("day")      # day: 0 for Monday, 1 for Tuesday

# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
WORK_START = 540
WORK_END = 1020

solver = Solver()
solver.add(start >= WORK_START, start + duration <= WORK_END)
solver.add(Or(day == 0, day == 1))

# Deborah is busy all day on Monday, so the meeting must be on Tuesday.
solver.add(day == 1)

# Busy schedules (in minutes from midnight):

# Jason's busy times on Tuesday:
#   11:30 to 12:00 -> (690, 720)
#   13:30 to 14:00 -> (810, 840)
jason_tuesday_busy = [
    (690, 720),
    (810, 840)
]

# Deborah's busy times on Tuesday:
#   9:00 to 11:00   -> (540, 660)
#   11:30 to 13:30  -> (690, 810)
#   14:00 to 17:00  -> (840, 1020)
deborah_tuesday_busy = [
    (540, 660),
    (690, 810),
    (840, 1020)
]

# Helper function: meeting interval [start, start+duration) must not overlap busy interval [busy_start, busy_end)
def non_overlap(busy_start, busy_end):
    return Or(start + duration <= busy_start, start >= busy_end)

# Add busy constraints for Jason on Tuesday:
for b_start, b_end in jason_tuesday_busy:
    solver.add(Implies(day == 1, non_overlap(b_start, b_end)))

# Add busy constraints for Deborah on Tuesday:
for b_start, b_end in deborah_tuesday_busy:
    solver.add(Implies(day == 1, non_overlap(b_start, b_end)))

# Iterate over possible start times (in minutes) within work hours to find a valid meeting time.
found = False
meeting_start = None
meeting_day = None

for t in range(WORK_START, WORK_END - duration + 1):
    solver.push()
    solver.add(start == t)
    if solver.check() == sat:
        model = solver.model()
        meeting_start = model[start].as_long()
        meeting_day = model[day].as_long()  # this will be 1 for Tuesday
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