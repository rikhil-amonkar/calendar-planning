from z3 import Solver, Int, Or, Implies, sat

# Meeting parameters
duration = 30  # duration in minutes
start = Int("start")  # meeting start time in minutes since midnight
day = Int("day")      # day: 0 for Monday, 1 for Tuesday

# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
WORK_START = 540
WORK_END   = 1020

solver = Solver()
solver.add(start >= WORK_START, start + duration <= WORK_END)
solver.add(Or(day == 0, day == 1))

# Ralph's busy schedule:
# Monday busy intervals (in minutes)
ralph_monday_busy = [
    (540, 570),   # 9:00 to 9:30
    (630, 660),   # 10:30 to 11:00
    (690, 720),   # 11:30 to 12:00
    (780, 810),   # 13:00 to 13:30
    (870, 900),   # 14:30 to 15:00
    (960, 1020)   # 16:00 to 17:00
]
# Tuesday busy intervals
ralph_tuesday_busy = [
    (600, 660),   # 10:00 to 11:00
    (810, 900)    # 13:30 to 15:00
]

# Patricia's busy schedule:
# Monday busy intervals
patricia_monday_busy = [
    (540, 690),   # 9:00 to 11:30
    (720, 840),   # 12:00 to 14:00
    (870, 960)    # 14:30 to 16:00
]
# Tuesday busy intervals
patricia_tuesday_busy = [
    (630, 720),   # 10:30 to 12:00
    (810, 900),   # 13:30 to 15:00
    (960, 1020)   # 16:00 to 17:00
]

# A helper function that returns a constraint ensuring that the meeting
# time [start, start+duration) does not overlap with a busy interval [busy_start, busy_end)
def non_overlap(busy_start, busy_end):
    return Or(start + duration <= busy_start, start >= busy_end)

# Add busy constraints for Ralph on Monday and Tuesday
for b_start, b_end in ralph_monday_busy:
    solver.add(Implies(day == 0, non_overlap(b_start, b_end)))
for b_start, b_end in ralph_tuesday_busy:
    solver.add(Implies(day == 1, non_overlap(b_start, b_end)))

# Add busy constraints for Patricia on Monday and Tuesday
for b_start, b_end in patricia_monday_busy:
    solver.add(Implies(day == 0, non_overlap(b_start, b_end)))
for b_start, b_end in patricia_tuesday_busy:
    solver.add(Implies(day == 1, non_overlap(b_start, b_end)))

# We want the meeting at the earliest availability.
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