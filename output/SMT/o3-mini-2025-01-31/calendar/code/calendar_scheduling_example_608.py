from z3 import Solver, Int, Or, Implies, sat

# Meeting parameters:
duration = 30  # meeting duration in minutes
start = Int("start")  # meeting start time (in minutes since midnight)
day = Int("day")      # day: 0 for Monday, 1 for Tuesday

# Work hours: from 9:00 (540 minutes) to 17:00 (1020 minutes)
WORK_START = 540
WORK_END = 1020

solver = Solver()
solver.add(start >= WORK_START, start + duration <= WORK_END)
solver.add(Or(day == 0, day == 1))

# Doris's busy intervals:
# Monday busy intervals: 9:00 to 15:30 and 16:00 to 17:00
doris_monday_busy = [
    (540, 930),     # 9:00 - 15:30
    (960, 1020)     # 16:00 - 17:00
]
# Tuesday busy intervals: 9:00 to 11:00 and 11:30 to 17:00
doris_tuesday_busy = [
    (540, 660),     # 9:00 - 11:00
    (690, 1020)     # 11:30 - 17:00
]

# Jessica is free the entire week, but she would like to avoid more meetings on Monday.
# Hence, we add a constraint to prefer Tuesday:
solver.add(day == 1)

# Helper function to enforce non-overlap between meeting and a busy interval.
def non_overlap(busy_start, busy_end):
    # Meeting time [start, start+duration) must not overlap with [busy_start, busy_end)
    return Or(start + duration <= busy_start, start >= busy_end)

# Add Doris's busy constraints.
for b_start, b_end in doris_monday_busy:
    solver.add(Implies(day == 0, non_overlap(b_start, b_end)))
for b_start, b_end in doris_tuesday_busy:
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