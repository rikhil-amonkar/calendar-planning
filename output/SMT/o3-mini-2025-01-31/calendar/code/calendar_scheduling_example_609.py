from z3 import Solver, Int, Or, Implies, sat

# Meeting parameters
duration = 30  # in minutes
start = Int("start")  # start time in minutes since midnight
day = Int("day")      # day: 0 for Monday, 1 for Tuesday

# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
WORK_START = 540
WORK_END = 1020

solver = Solver()
solver.add(start >= WORK_START, start + duration <= WORK_END)
solver.add(Or(day == 0, day == 1))

# Emily's busy schedule:
# Monday busy intervals:
#   10:30 to 11:00  -> (630, 660)
#   11:30 to 12:00  -> (690, 720)
#   13:30 to 14:00  -> (810, 840)
#   14:30 to 15:00  -> (870, 900)
#   16:00 to 17:00  -> (960, 1020)
emily_monday_busy = [
    (630, 660),
    (690, 720),
    (810, 840),
    (870, 900),
    (960, 1020)
]
# Tuesday busy intervals:
#   9:30 to 10:00   -> (570, 600)
#   11:00 to 12:00  -> (660, 720)
#   16:30 to 17:00  -> (990, 1020)
emily_tuesday_busy = [
    (570, 600),
    (660, 720),
    (990, 1020)
]

# Zachary's busy schedule:
# Monday busy intervals:
#   9:00 to 11:00   -> (540, 660)
#   11:30 to 14:30  -> (690, 870)
#   15:00 to 17:00  -> (900, 1020)
zachary_monday_busy = [
    (540, 660),
    (690, 870),
    (900, 1020)
]
# Tuesday busy intervals:
#   9:00 to 13:00   -> (540, 780)
#   13:30 to 14:30  -> (810, 870)
#   15:00 to 15:30  -> (900, 930)
#   16:00 to 16:30  -> (960, 990)
zachary_tuesday_busy = [
    (540, 780),
    (810, 870),
    (900, 930),
    (960, 990)
]

# Zachary would rather not meet on Tuesday, so add constraint to meet on Monday
solver.add(day == 0)

def non_overlap(busy_start, busy_end):
    # Meeting [start, start+duration) must not overlap with busy interval [busy_start, busy_end)
    return Or(start + duration <= busy_start, start >= busy_end)

# Add constraints for Emily's busy schedule:
for b_start, b_end in emily_monday_busy:
    solver.add(Implies(day == 0, non_overlap(b_start, b_end)))
for b_start, b_end in emily_tuesday_busy:
    solver.add(Implies(day == 1, non_overlap(b_start, b_end)))

# Add constraints for Zachary's busy schedule:
for b_start, b_end in zachary_monday_busy:
    solver.add(Implies(day == 0, non_overlap(b_start, b_end)))
for b_start, b_end in zachary_tuesday_busy:
    solver.add(Implies(day == 1, non_overlap(b_start, b_end)))

# Find an earliest meeting time that satisfies all constraints.
found = False
result_start = None

for t in range(WORK_START, WORK_END - duration + 1):
    solver.push()
    solver.add(start == t)
    if solver.check() == sat:
        model = solver.model()
        result_start = model[start].as_long()
        chosen_day = model[day].as_long()
        day_str = "Monday" if chosen_day == 0 else "Tuesday"
        found = True
        solver.pop()
        break
    solver.pop()

if found:
    meeting_end = result_start + duration
    sh, sm = divmod(result_start, 60)
    eh, em = divmod(meeting_end, 60)
    print(f"A valid meeting time is on {day_str} from {sh:02d}:{sm:02d} to {eh:02d}:{em:02d}.")
else:
    print("No valid meeting time could be found.")