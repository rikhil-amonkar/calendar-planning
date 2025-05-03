from z3 import Solver, Int, Or, Implies, sat

# Meeting parameters.
duration = 30  # meeting duration in minutes
start = Int("start")  # meeting start time in minutes since midnight
day = Int("day")      # day: 0 for Monday, 1 for Tuesday

# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
WORK_START = 540
WORK_END = 1020

solver = Solver()
solver.add(start >= WORK_START, start + duration <= WORK_END)
solver.add(Or(day == 0, day == 1))

# Albert's schedule and preference.
# Albert's busy intervals (only on Tuesday):
# Tuesday busy:
#   10:00 to 10:30 -> (600, 630)
#   11:00 to 11:30 -> (660, 690)
#   12:30 to 13:00 -> (750, 780)
#   13:30 to 15:00 -> (810, 900)
#   15:30 to 16:00 -> (930, 960)
#   16:30 to 17:00 -> (990, 1020)
albert_tuesday_busy = [
    (600, 630),
    (660, 690),
    (750, 780),
    (810, 900),
    (930, 960),
    (990, 1020)
]
# Additionally, Albert cannot meet on Monday after 11:00.
# That is, if day==0 (Monday), meeting must end by 11:00 (i.e. start + duration <= 660).
solver.add(Implies(day == 0, start + duration <= 660))

# Denise's schedule.
# Denise's busy intervals on Monday:
#   9:00 to 9:30 -> (540, 570)
#   10:30 to 11:30 -> (630, 690)
#   12:00 to 13:00 -> (720, 780)
#   13:30 to 14:00 -> (810, 840)
#   15:00 to 16:00 -> (900, 960)
#   16:30 to 17:00 -> (990, 1020)
denise_monday_busy = [
    (540, 570),
    (630, 690),
    (720, 780),
    (810, 840),
    (900, 960),
    (990, 1020)
]
# Denise's busy intervals on Tuesday:
#   9:00 to 12:30 -> (540, 750)
#   13:00 to 13:30 -> (780, 810)
#   14:00 to 16:30 -> (840, 990)
denise_tuesday_busy = [
    (540, 750),
    (780, 810),
    (840, 990)
]

# Helper function to express that the meeting interval [start, start+duration)
# does not overlap with a given busy interval [b_start, b_end).
def non_overlap(b_start, b_end):
    return Or(start + duration <= b_start, start >= b_end)

# Add busy constraints for Albert.
# For Tuesday:
for b_start, b_end in albert_tuesday_busy:
    solver.add(Implies(day == 1, non_overlap(b_start, b_end)))
# (Albert has no busy intervals on Monday apart from his meeting time constraint.)

# Add busy constraints for Denise.
# For Monday:
for b_start, b_end in denise_monday_busy:
    solver.add(Implies(day == 0, non_overlap(b_start, b_end)))
# For Tuesday:
for b_start, b_end in denise_tuesday_busy:
    solver.add(Implies(day == 1, non_overlap(b_start, b_end)))

# Search for an earliest meeting time within the work hours satisfying all constraints.
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