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

# Jeffrey is free the entire week, so no constraints for him.

# Harold's busy schedule in minutes from midnight:
# Monday:
#   9:00 to 10:00   -> (540, 600)
#   10:30 to 17:00  -> (630, 1020)
harold_monday_busy = [(540, 600), (630, 1020)]
# Tuesday:
#   9:00 to 9:30   -> (540, 570)
#   10:30 to 11:30 -> (630, 690)
#   12:30 to 13:30 -> (750, 810)
#   14:30 to 15:30 -> (870, 930)
#   16:00 to 17:00 -> (960, 1020)
harold_tuesday_busy = [(540, 570), (630, 690), (750, 810), (870, 930), (960, 1020)]

# Helper function: meeting [start, start+duration) must not overlap busy interval [busy_start, busy_end)
def non_overlap(busy_start, busy_end):
    return Or(start + duration <= busy_start, start >= busy_end)

# Add Harold's busy time constraints for Monday:
for b_start, b_end in harold_monday_busy:
    solver.add(Implies(day == 0, non_overlap(b_start, b_end)))
    
# Add Harold's busy time constraints for Tuesday:
for b_start, b_end in harold_tuesday_busy:
    solver.add(Implies(day == 1, non_overlap(b_start, b_end)))

# Additional scheduling preferences:
# 1. Harold would like to avoid more meetings on Monday.
#    (So we try Tuesday first and only fall back to Monday if necessary.)
# 2. On Tuesday, Harold prefers meetings to be scheduled before 14:30.
#    That means the meeting should finish by 14:30 (which is 870 minutes from midnight).
solver.add(Implies(day == 1, start + duration <= 870))

# We now try to find a solution.
# First, attempt to schedule on Tuesday (day == 1) as preferred.
found = False
meeting_start = None
meeting_day = None

for t in range(WORK_START, WORK_END - duration + 1):
    solver.push()
    solver.add(start == t, day == 1)
    if solver.check() == sat:
        model = solver.model()
        meeting_start = model[start].as_long()
        meeting_day = model[day].as_long()  # should be 1 for Tuesday
        found = True
        solver.pop()
        break
    solver.pop()

# If no Tuesday slot is found, then try Monday.
if not found:
    for t in range(WORK_START, WORK_END - duration + 1):
        solver.push()
        solver.add(start == t, day == 0)
        if solver.check() == sat:
            model = solver.model()
            meeting_start = model[start].as_long()
            meeting_day = model[day].as_long()  # should be 0 for Monday
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