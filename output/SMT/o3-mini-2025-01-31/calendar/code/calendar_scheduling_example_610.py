from z3 import Solver, Int, Or, Implies, sat

# Meeting parameters
duration = 30  # duration in minutes
start = Int("start")  # meeting start time in minutes since midnight
day = Int("day")      # day: 0 for Monday, 1 for Tuesday

# Work hours: 9:00 (540) to 17:00 (1020)
WORK_START = 540
WORK_END   = 1020

solver = Solver()
solver.add(start >= WORK_START, start + duration <= WORK_END)
solver.add(Or(day == 0, day == 1))

# Given Patrick cannot meet on Monday.
solver.add(day == 1)   # therefore, meeting is on Tuesday

# Additional constraint for Richard:
# "Richard would rather not meet on Tuesday after 14:00"
# i.e. if Tuesday then meeting must finish by 14:00 (840 minutes)
solver.add(Implies(day == 1, start + duration <= 840))

# Define Patrick's busy schedule on Tuesday
# Tuesday busy intervals:
#   9:30 to 10:00   -> (570, 600)
#   11:00 to 11:30  -> (660, 690)
#   12:30 to 13:00  -> (750, 780)
#   16:00 to 17:00  -> (960, 1020)
patrick_tuesday_busy = [
    (570, 600),
    (660, 690),
    (750, 780),
    (960, 1020)
]

# Define Richard's busy schedule on Tuesday
# Tuesday busy intervals:
#   9:00 to 9:30   -> (540, 570)
#   10:00 to 11:00  -> (600, 660)
#   11:30 to 13:30  -> (690, 810)
#   14:00 to 15:00  -> (840, 900)
#   15:30 to 16:00  -> (930, 960)
#   16:30 to 17:00  -> (990, 1020)
richard_tuesday_busy = [
    (540, 570),
    (600, 660),
    (690, 810),
    (840, 900),
    (930, 960),
    (990, 1020)
]

# Helper function: meeting [start, start+duration) should not overlap
# with a busy interval [busy_start, busy_end)
def non_overlap(busy_start, busy_end):
    return Or(start + duration <= busy_start, start >= busy_end)

# Add Patrick's busy constraints for Tuesday
for b_start, b_end in patrick_tuesday_busy:
    solver.add(Implies(day == 1, non_overlap(b_start, b_end)))

# Add Richard's busy constraints for Tuesday
for b_start, b_end in richard_tuesday_busy:
    solver.add(Implies(day == 1, non_overlap(b_start, b_end)))

# Find an earliest meeting start time that satisfies all constraints.
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