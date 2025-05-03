from z3 import Solver, Int, Or, Implies, sat

# Meeting parameters
duration = 30  # meeting duration in minutes
start = Int("start")  # meeting start time (minutes after midnight)
day = Int("day")      # day: 0 for Monday, 1 for Tuesday

# Work hours: from 9:00 (540 minutes) to 17:00 (1020 minutes)
WORK_START = 540
WORK_END = 1020

# Create a solver and add basic constraints
solver = Solver()
solver.add(start >= WORK_START, start + duration <= WORK_END)
solver.add(Or(day == 0, day == 1))  # day is either Monday (0) or Tuesday (1)

# Raymond's busy schedule (in minutes from midnight)
# Monday:
#   9:00 to 10:00 -> (540, 600)
#   12:00 to 12:30 -> (720, 750)
#   13:30 to 14:30 -> (810, 870)
#   16:00 to 16:30 -> (960, 990)
raymond_monday = [
    (540, 600),
    (720, 750),
    (810, 870),
    (960, 990)
]
# Tuesday:
#   9:00 to 10:30 -> (540, 630)
#   13:30 to 14:30 -> (810, 870)
#   16:00 to 16:30 -> (960, 990)
raymond_tuesday = [
    (540, 630),
    (810, 870),
    (960, 990)
]

# Gerald's busy schedule (in minutes)
# Monday:
#   9:00 to 10:30 -> (540, 630)
#   11:00 to 14:00 -> (660, 840)
#   14:30 to 15:00 -> (870, 900)
#   15:30 to 17:00 -> (930, 1020)
gerald_monday = [
    (540, 630),
    (660, 840),
    (870, 900),
    (930, 1020)
]
# Tuesday:
#   9:00 to 10:30 -> (540, 630)
#   11:00 to 13:00 -> (660, 780)
#   13:30 to 14:30 -> (810, 870)
#   15:00 to 17:00 -> (900, 1020)
gerald_tuesday = [
    (540, 630),
    (660, 780),
    (810, 870),
    (900, 1020)
]

# Raymond would like to avoid more meetings on Tuesday.
# So if a Monday slot exists, we prefer that.
#
# Helper function: meeting slot [start, start+duration) must not overlap a busy interval.
def non_overlap(busy_start, busy_end):
    return Or(start + duration <= busy_start, start >= busy_end)

# Add Raymond's constraints for both days.
for b_start, b_end in raymond_monday:
    solver.add(Implies(day == 0, non_overlap(b_start, b_end)))
for b_start, b_end in raymond_tuesday:
    solver.add(Implies(day == 1, non_overlap(b_start, b_end)))

# Add Gerald's constraints for both days.
for b_start, b_end in gerald_monday:
    solver.add(Implies(day == 0, non_overlap(b_start, b_end)))
for b_start, b_end in gerald_tuesday:
    solver.add(Implies(day == 1, non_overlap(b_start, b_end)))

# We want to schedule the meeting at the earliest availability.
# Also, we prefer Monday (day == 0) whenever possible.
found = False
meeting_start = None
meeting_day = None

# First, try to find an available slot on Monday.
for t in range(WORK_START, WORK_END - duration + 1):
    solver.push()
    solver.add(start == t, day == 0)  # force Monday
    if solver.check() == sat:
        model = solver.model()
        meeting_start = model[start].as_long()
        meeting_day = model[day].as_long()  # should be 0 (Monday)
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
            meeting_day = model[day].as_long()  # should be 1 (Tuesday)
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