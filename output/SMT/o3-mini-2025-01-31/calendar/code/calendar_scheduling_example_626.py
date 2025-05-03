from z3 import Solver, Int, Or, Implies, sat

# Meeting parameters:
duration = 60  # meeting duration is 60 minutes (1 hour)
start = Int("start")  # meeting start time in minutes from midnight
day = Int("day")      # day: 0 for Monday, 1 for Tuesday

# Work hours: from 9:00 (540 minutes) to 17:00 (1020 minutes)
WORK_START = 540
WORK_END = 1020

solver = Solver()
solver.add(start >= WORK_START, start + duration <= WORK_END)
solver.add(Or(day == 0, day == 1))

# Patricia's busy schedule (in minutes from midnight):
# Monday:
#   10:00 to 10:30 -> (600, 630)
#   11:30 to 12:00 -> (690, 720)
#   13:00 to 13:30 -> (780, 810)
#   14:30 to 15:30 -> (870, 930)
#   16:00 to 16:30 -> (960, 990)
patricia_monday_busy = [(600, 630), (690, 720), (780, 810), (870, 930), (960, 990)]
# Tuesday:
#   10:00 to 10:30 -> (600, 630)
#   11:00 to 12:00 -> (660, 720)
#   14:00 to 16:00 -> (840, 960)
#   16:30 to 17:00 -> (990, 1020)
patricia_tuesday_busy = [(600, 630), (660, 720), (840, 960), (990, 1020)]

# Jesse's busy schedule:
# Monday: entire day busy from 9:00 to 17:00 -> (540, 1020)
jesse_monday_busy = [(540, 1020)]
# Tuesday:
#   11:00 to 11:30 -> (660, 690)
#   12:00 to 12:30 -> (720, 750)
#   13:00 to 14:00 -> (780, 840)
#   14:30 to 15:00 -> (870, 900)
#   15:30 to 17:00 -> (930, 1020)
jesse_tuesday_busy = [(660, 690), (720, 750), (780, 840), (870, 900), (930, 1020)]

# Helper function to express that a meeting does not overlap a busy slot.
def non_overlap(busy_start, busy_end):
    # Meeting [start, start+duration) must end on or before the busy slot starts,
    # or start on or after the busy slot ends.
    return Or(start + duration <= busy_start, start >= busy_end)

# Add Patricia's busy schedule constraints:
for b_start, b_end in patricia_monday_busy:
    solver.add(Implies(day == 0, non_overlap(b_start, b_end)))
for b_start, b_end in patricia_tuesday_busy:
    solver.add(Implies(day == 1, non_overlap(b_start, b_end)))

# Add Jesse's busy schedule constraints:
for b_start, b_end in jesse_monday_busy:
    solver.add(Implies(day == 0, non_overlap(b_start, b_end)))
for b_start, b_end in jesse_tuesday_busy:
    solver.add(Implies(day == 1, non_overlap(b_start, b_end)))

# Since Jesse is completely busy on Monday, the meeting will have to be on Tuesday.
# (No additional preference is given, so we let the solver decide based on constraints.)

# Try to find a valid meeting time:
found = False
meeting_start = None
meeting_day = None

# Iterate through possible start times
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