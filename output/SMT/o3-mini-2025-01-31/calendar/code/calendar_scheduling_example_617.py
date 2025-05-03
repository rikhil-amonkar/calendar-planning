from z3 import Solver, Int, Or, Implies, sat

# Meeting parameters
duration = 60  # meeting duration in minutes (1 hour)
start = Int("start")  # meeting start time in minutes since midnight
day = Int("day")      # day: 0 for Monday, 1 for Tuesday

# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
WORK_START = 540
WORK_END = 1020

# Create a Z3 solver and add basic constraints
solver = Solver()
solver.add(start >= WORK_START, start + duration <= WORK_END)
solver.add(Or(day == 0, day == 1))

# Stephen's busy schedule (in minutes):
# Monday:
#   12:30 to 13:30 -> (750, 810)
#   16:30 to 17:00 -> (990, 1020)
stephen_monday_busy = [(750, 810), (990, 1020)]
# Tuesday:
#   11:00 to 11:30 -> (660, 690)
#   13:30 to 14:00 -> (810, 840)
#   16:00 to 16:30 -> (960, 990)
stephen_tuesday_busy = [(660, 690), (810, 840), (960, 990)]

# Robert's busy schedule (in minutes):
# Monday:
#   9:00 to 10:30    -> (540, 630)
#   11:00 to 12:00   -> (660, 720)
#   12:30 to 15:00   -> (750, 900)
#   16:30 to 17:00   -> (990, 1020)
robert_monday_busy = [(540, 630), (660, 720), (750, 900), (990, 1020)]
# Tuesday:
#   9:00 to 11:30    -> (540, 690)
#   12:00 to 13:30   -> (720, 810)
#   14:00 to 15:30   -> (840, 930)
robert_tuesday_busy = [(540, 690), (720, 810), (840, 930)]

# Helper function: Ensure meeting [start, start+duration) does not overlap busy interval [busy_start, busy_end)
def non_overlap(busy_start, busy_end):
    return Or(start + duration <= busy_start, start >= busy_end)

# Add Stephen's busy constraints
for b_start, b_end in stephen_monday_busy:
    solver.add(Implies(day == 0, non_overlap(b_start, b_end)))
for b_start, b_end in stephen_tuesday_busy:
    solver.add(Implies(day == 1, non_overlap(b_start, b_end)))

# Add Robert's busy constraints
for b_start, b_end in robert_monday_busy:
    solver.add(Implies(day == 0, non_overlap(b_start, b_end)))
for b_start, b_end in robert_tuesday_busy:
    solver.add(Implies(day == 1, non_overlap(b_start, b_end)))

# We want the meeting at the earliest availability.
# We'll check for an available time slot starting from WORK_START.
found = False
meeting_start = None
meeting_day = None

# We'll enumerate possible starting times and try both days (Monday first for earliest time).
# Try Monday first
for t in range(WORK_START, WORK_END - duration + 1):
    solver.push()
    solver.add(start == t, day == 0)  # force Monday
    if solver.check() == sat:
        model = solver.model()
        meeting_start = model[start].as_long()
        meeting_day = model[day].as_long()  # should be 0 for Monday
        found = True
        solver.pop()
        break
    solver.pop()

# If no valid slot on Monday, try Tuesday.
if not found:
    for t in range(WORK_START, WORK_END - duration + 1):
        solver.push()
        solver.add(start == t, day == 1)  # force Tuesday
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