from z3 import Solver, Int, Or, Implies, sat

# Meeting parameters:
duration = 30  # meeting duration of 30 minutes
start = Int("start")  # meeting start time in minutes from midnight
day = Int("day")      # day: 0 for Monday, 1 for Tuesday

# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
WORK_START = 540
WORK_END = 1020

solver = Solver()
solver.add(start >= WORK_START, start + duration <= WORK_END)
solver.add(Or(day == 0, day == 1))

# Shirley's busy schedule (in minutes from midnight):
# Monday:
#   10:30 to 12:00 -> (630, 720)
#   14:30 to 16:00 -> (870, 960)
shirley_monday_busy = [(630, 720), (870, 960)]
# Tuesday:
#   9:30 to 10:30  -> (570, 630)
#   11:30 to 12:00 -> (690, 720)
#   13:30 to 14:00 -> (810, 840)
#   14:30 to 15:00 -> (870, 900)
#   16:00 to 16:30 -> (960, 990)
shirley_tuesday_busy = [(570, 630), (690, 720), (810, 840), (870, 900), (960, 990)]

# Adam's busy schedule (in minutes from midnight):
# Monday:
#   9:30 to 11:30  -> (570, 690)
#   14:00 to 16:00 -> (840, 960)
#   16:30 to 17:00 -> (990, 1020)
adam_monday_busy = [(570, 690), (840, 960), (990, 1020)]
# Tuesday:
#   9:00 to 9:30   -> (540, 570)
#   10:00 to 12:00 -> (600, 720)
#   12:30 to 13:00 -> (750, 780)
#   14:00 to 16:30 -> (840, 990)
adam_tuesday_busy = [(540, 570), (600, 720), (750, 780), (840, 990)]

# Additional constraint: Adam cannot meet on Monday after 10:00.
# This means if the meeting is on Monday (day==0), it must end by 10:00 (600 minutes).
solver.add(Implies(day == 0, start + duration <= 600))

# Helper function: the meeting [start, start+duration) must not overlap a busy interval [busy_start, busy_end)
def non_overlap(busy_start, busy_end):
    return Or(start + duration <= busy_start, start >= busy_end)

# Add Shirley's busy schedule constraints:
for b_start, b_end in shirley_monday_busy:
    solver.add(Implies(day == 0, non_overlap(b_start, b_end)))
for b_start, b_end in shirley_tuesday_busy:
    solver.add(Implies(day == 1, non_overlap(b_start, b_end)))

# Add Adam's busy schedule constraints:
for b_start, b_end in adam_monday_busy:
    solver.add(Implies(day == 0, non_overlap(b_start, b_end)))
for b_start, b_end in adam_tuesday_busy:
    solver.add(Implies(day == 1, non_overlap(b_start, b_end)))

# Now, try to find a valid meeting time.
found = False
meeting_start = None
meeting_day = None

# We iterate over possible start times in 1 minute increments.
for t in range(WORK_START, WORK_END - duration + 1):
    solver.push()
    solver.add(start == t)
    if solver.check() == sat:
        model = solver.model()
        meeting_start = model[start].as_long()
        meeting_day = model[day].as_long()  # 0 for Monday, 1 for Tuesday
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