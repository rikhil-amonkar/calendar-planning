from z3 import Solver, Int, Or, Implies, sat

# Meeting parameters
duration = 30  # meeting duration in minutes
start = Int("start")  # meeting start time in minutes since midnight
day = Int("day")      # day: 0 for Monday, 1 for Tuesday

# Work hours: 9:00 (540 mins) to 17:00 (1020 mins)
WORK_START = 540
WORK_END = 1020

solver = Solver()
solver.add(start >= WORK_START, start + duration <= WORK_END)
solver.add(Or(day == 0, day == 1))

# Joshua does not want to meet on Tuesday, so force meeting on Monday.
solver.add(day == 0)

# Ann does not want to meet on Monday after 11:00.
# That is, if meeting is on Monday then it must finish by 11:00 (660 minutes).
solver.add(Implies(day == 0, start + duration <= 660))

# Busy intervals for each participant on Monday (times in minutes since midnight):

# Ann's busy intervals on Monday:
#   13:30 to 14:30 -> (810, 870)
ann_monday_busy = [
    (810, 870)
]

# Joshua's busy intervals on Monday:
#   10:00 to 11:00 -> (600, 660)
#   11:30 to 12:30 -> (690, 750)
#   14:00 to 16:00 -> (840, 960)
joshua_monday_busy = [
    (600, 660),
    (690, 750),
    (840, 960)
]

# Helper function ensuring meeting interval [start, start+duration)
# does not overlap with a busy interval [busy_start, busy_end)
def non_overlap(busy_start, busy_end):
    return Or(start + duration <= busy_start, start >= busy_end)

# Add Ann's busy constraints for Monday
for b_start, b_end in ann_monday_busy:
    solver.add(Implies(day == 0, non_overlap(b_start, b_end)))

# Add Joshua's busy constraints for Monday
for b_start, b_end in joshua_monday_busy:
    solver.add(Implies(day == 0, non_overlap(b_start, b_end)))

# Try to find the earliest meeting start time that satisfies all constraints.
found = False
meeting_start = None
for t in range(WORK_START, WORK_END - duration + 1):
    solver.push()
    solver.add(start == t)
    if solver.check() == sat:
        model = solver.model()
        meeting_start = model[start].as_long()
        chosen_day = model[day].as_long()
        day_str = "Monday" if chosen_day == 0 else "Tuesday"
        found = True
        solver.pop()
        break
    solver.pop()

if found:
    meeting_end = meeting_start + duration
    sh, sm = divmod(meeting_start, 60)
    eh, em = divmod(meeting_end, 60)
    print(f"A valid meeting time is on {day_str} from {sh:02d}:{sm:02d} to {eh:02d}:{em:02d}.")
else:
    print("No valid meeting time could be found.")