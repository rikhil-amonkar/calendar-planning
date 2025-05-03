from z3 import Solver, Int, Or, Implies, sat

# Meeting parameters
duration = 30  # meeting duration in minutes
start = Int("start")  # meeting start time (in minutes after midnight)
day = Int("day")      # day: 0 for Monday, 1 for Tuesday

# Work hours (in minutes): 9:00 (540) to 17:00 (1020)
WORK_START = 540
WORK_END = 1020

# Create the Z3 solver and add basic constraints
solver = Solver()
solver.add(start >= WORK_START, start + duration <= WORK_END)
solver.add(Or(day == 0, day == 1))

# Busy intervals for each participant are given as (start, end) in minutes.

# Emily's busy schedule:
# Monday:
#   12:30 to 13:00 -> (750, 780)
#   13:30 to 14:00 -> (810, 840)
#   16:30 to 17:00 -> (990, 1020)
# Tuesday:
#   9:30 to 10:00  -> (570, 600)
#   11:30 to 12:00 -> (690, 720)
#   12:30 to 13:30 -> (750, 810)
#   15:30 to 16:00 -> (930, 960)
emily_monday_busy = [(750, 780), (810, 840), (990, 1020)]
emily_tuesday_busy = [(570, 600), (690, 720), (750, 810), (930, 960)]

# Sandra's busy schedule:
# Monday:
#   9:00 to 11:00   -> (540, 660)
#   11:30 to 17:00  -> (690, 1020)
# Tuesday:
#   9:30 to 10:30   -> (570, 630)
#   11:00 to 13:00  -> (660, 780)
#   13:30 to 14:00  -> (810, 840)
#   15:00 to 16:00  -> (900, 960)
sandra_monday_busy = [(540, 660), (690, 1020)]
sandra_tuesday_busy = [(570, 630), (660, 780), (810, 840), (900, 960)]

# Helper function: The meeting time [start, start+duration) must not overlap a busy interval [busy_start, busy_end)
def non_overlap(busy_start, busy_end):
    return Or(start + duration <= busy_start, start >= busy_end)

# Add constraints for Emily's schedule on Monday and Tuesday
for b_start, b_end in emily_monday_busy:
    solver.add(Implies(day == 0, non_overlap(b_start, b_end)))
for b_start, b_end in emily_tuesday_busy:
    solver.add(Implies(day == 1, non_overlap(b_start, b_end)))

# Add constraints for Sandra's schedule on Monday and Tuesday
for b_start, b_end in sandra_monday_busy:
    solver.add(Implies(day == 0, non_overlap(b_start, b_end)))
for b_start, b_end in sandra_tuesday_busy:
    solver.add(Implies(day == 1, non_overlap(b_start, b_end)))

# Emily would rather not meet on Tuesday, so we try Monday first to meet at the earliest availability.
found = False
meeting_start = None
meeting_day = None

# First, try to find an available slot on Monday (day == 0)
for t in range(WORK_START, WORK_END - duration + 1):
    solver.push()
    solver.add(start == t, day == 0)  # force Monday
    if solver.check() == sat:
        model = solver.model()
        meeting_start = model[start].as_long()
        meeting_day = model[day].as_long()  # should be 0
        found = True
        solver.pop()
        break
    solver.pop()

# If no Monday slot is found, try Tuesday.
if not found:
    for t in range(WORK_START, WORK_END - duration + 1):
        solver.push()
        solver.add(start == t, day == 1)  # force Tuesday
        if solver.check() == sat:
            model = solver.model()
            meeting_start = model[start].as_long()
            meeting_day = model[day].as_long()  # should be 1
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