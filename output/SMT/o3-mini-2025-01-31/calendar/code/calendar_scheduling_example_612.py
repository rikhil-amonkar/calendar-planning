from z3 import Solver, Int, Or, Implies, sat

# Meeting parameters
duration = 30  # meeting duration in minutes
start = Int("start")  # meeting start time in minutes since midnight
day = Int("day")      # day: 0 for Monday, 1 for Tuesday

# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
WORK_START = 540
WORK_END = 1020

solver = Solver()
solver.add(start >= WORK_START, start + duration <= WORK_END)
solver.add(Or(day == 0, day == 1))

# Joshua's busy schedule:
# Monday: 11:30 to 12:00 -> (690, 720)
joshua_monday_busy = [
    (690, 720)
]
# Tuesday: 9:00 to 9:30, 14:00 to 14:30, 16:00 to 16:30 
# i.e., (540, 570), (840, 870), (960, 990)
joshua_tuesday_busy = [
    (540, 570),
    (840, 870),
    (960, 990)
]

# Diane's busy schedule:
# Monday: 9:30 to 10:30, 11:00 to 14:00, 15:00 to 16:30 
# i.e., (570, 630), (660, 840), (900, 990)
diane_monday_busy = [
    (570, 630),
    (660, 840),
    (900, 990)
]
# Tuesday: 9:00 to 10:00, 10:30 to 11:00, 11:30 to 12:00,
#          13:00 to 14:30, 15:30 to 16:30
# i.e., (540, 600), (630, 660), (690, 720), (780, 870), (930, 990)
diane_tuesday_busy = [
    (540, 600),
    (630, 660),
    (690, 720),
    (780, 870),
    (930, 990)
]

# Helper function to ensure that the meeting interval [start, start+duration)
# does not overlap with a given busy interval [busy_start, busy_end)
def non_overlap(busy_start, busy_end):
    return Or(start + duration <= busy_start, start >= busy_end)

# Add busy constraints for Joshua
for b_start, b_end in joshua_monday_busy:
    solver.add(Implies(day == 0, non_overlap(b_start, b_end)))
for b_start, b_end in joshua_tuesday_busy:
    solver.add(Implies(day == 1, non_overlap(b_start, b_end)))

# Add busy constraints for Diane
for b_start, b_end in diane_monday_busy:
    solver.add(Implies(day == 0, non_overlap(b_start, b_end)))
for b_start, b_end in diane_tuesday_busy:
    solver.add(Implies(day == 1, non_overlap(b_start, b_end)))

# We want to schedule the meeting at the earliest availability.
# We'll iterate over candidate start times (in minutes) from the start of work hours.
found = False
result_start = None
result_day = None

for t in range(WORK_START, WORK_END - duration + 1):
    solver.push()
    solver.add(start == t)
    if solver.check() == sat:
        model = solver.model()
        result_start = model[start].as_long()
        result_day = model[day].as_long()
        found = True
        solver.pop()
        break
    solver.pop()

if found:
    meeting_end = result_start + duration
    sh, sm = divmod(result_start, 60)
    eh, em = divmod(meeting_end, 60)
    day_str = "Monday" if result_day == 0 else "Tuesday"
    print(f"A valid meeting time is on {day_str} from {sh:02d}:{sm:02d} to {eh:02d}:{em:02d}.")
else:
    print("No valid meeting time could be found.")