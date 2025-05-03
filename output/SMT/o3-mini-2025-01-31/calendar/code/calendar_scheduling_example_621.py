from z3 import Solver, Int, Or, Implies, sat

# Meeting parameters
duration = 60  # meeting duration in minutes (1 hour)
start = Int("start")  # meeting start time in minutes from midnight
day = Int("day")      # day: 0 for Monday, 1 for Tuesday

# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
WORK_START = 540
WORK_END = 1020

# Create the Z3 solver and add basic constraints
solver = Solver()
solver.add(start >= WORK_START, start + duration <= WORK_END)
solver.add(Or(day == 0, day == 1))

# Define busy intervals for Harold and Bobby, in minutes from midnight

# Harold's busy schedule:
# Monday:
#   10:30 to 11:00 -> (630, 660)
#   13:30 to 14:00 -> (810, 840)
#   15:30 to 16:00 -> (930, 960)
#   16:30 to 17:00 -> (990, 1020)
harold_monday_busy = [(630, 660), (810, 840), (930, 960), (990, 1020)]
# Tuesday:
#   9:30 to 10:00  -> (570, 600)
#   11:30 to 12:00 -> (690, 720)
#   12:30 to 13:00 -> (750, 780)
#   14:00 to 15:30 -> (840, 930)
harold_tuesday_busy = [(570, 600), (690, 720), (750, 780), (840, 930)]

# Bobby's busy schedule:
# Monday:
#   9:30 to 11:00  -> (570, 660)
#   12:00 to 12:30 -> (720, 750)
#   13:00 to 13:30 -> (780, 810)
#   14:00 to 14:30 -> (840, 870)
#   15:30 to 17:00 -> (930, 1020)
bobby_monday_busy = [(570, 660), (720, 750), (780, 810), (840, 870), (930, 1020)]
# Tuesday:
#   9:30 to 10:00  -> (570, 600)
#   12:30 to 13:00 -> (750, 780)
#   14:00 to 15:30 -> (840, 930)
#   16:00 to 17:00 -> (960, 1020)
bobby_tuesday_busy = [(570, 600), (750, 780), (840, 930), (960, 1020)]

# A helper function to ensure the meeting interval [start, start+duration)
# does not overlap a busy interval [busy_start, busy_end)
def non_overlap(busy_start, busy_end):
    return Or(start + duration <= busy_start, start >= busy_end)

# Add constraints for Harold's busy schedule based on the day
for b_start, b_end in harold_monday_busy:
    solver.add(Implies(day == 0, non_overlap(b_start, b_end)))
for b_start, b_end in harold_tuesday_busy:
    solver.add(Implies(day == 1, non_overlap(b_start, b_end)))

# Add constraints for Bobby's busy schedule based on the day
for b_start, b_end in bobby_monday_busy:
    solver.add(Implies(day == 0, non_overlap(b_start, b_end)))
for b_start, b_end in bobby_tuesday_busy:
    solver.add(Implies(day == 1, non_overlap(b_start, b_end)))

# The group would like to meet at their earliest availability.
# We try to find the earliest time slot on Monday first, then Tuesday if necessary.
found = False
meeting_start = None
meeting_day = None

# Try Monday first (day == 0)
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

# If no valid slot is found on Monday, try Tuesday.
if not found:
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

if found:
    meeting_end = meeting_start + duration
    start_hour, start_min = divmod(meeting_start, 60)
    end_hour, end_min = divmod(meeting_end, 60)
    day_str = "Monday" if meeting_day == 0 else "Tuesday"
    print(f"A valid meeting time is on {day_str} from {start_hour:02d}:{start_min:02d} to {end_hour:02d}:{end_min:02d}.")
else:
    print("No valid meeting time could be found.")