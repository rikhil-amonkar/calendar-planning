from z3 import Solver, Int, Or, Implies, sat

# Meeting parameters.
duration = 30  # Meeting duration in minutes
start = Int("start")  # Start time in minutes since midnight
day = Int("day")      # Day: 0 for Monday, 1 for Tuesday

# Work hours: from 9:00 (540 minutes) to 17:00 (1020 minutes)
WORK_START = 540
WORK_END = 1020

solver = Solver()
solver.add(start >= WORK_START, start + duration <= WORK_END)
solver.add(Or(day == 0, day == 1))

# Participant busy schedules (in minutes since midnight)
# Amy's busy intervals:
# Monday: 10:00 to 11:00, 12:00 to 12:30, 15:30 to 17:00 
amy_monday_busy = [
    (600, 660),   # 10:00 - 11:00
    (720, 750),   # 12:00 - 12:30
    (930, 1020)   # 15:30 - 17:00
]
# Tuesday: 9:00 to 10:00, 11:30 to 12:00, 13:30 to 14:00, 15:30 to 16:00, 16:30 to 17:00 
amy_tuesday_busy = [
    (540, 600),   # 9:00 - 10:00
    (690, 720),   # 11:30 - 12:00
    (810, 840),   # 13:30 - 14:00
    (930, 960),   # 15:30 - 16:00
    (990, 1020)   # 16:30 - 17:00
]

# Denise's busy intervals:
# Monday: 9:00 to 9:30, 10:00 to 17:00 
denise_monday_busy = [
    (540, 570),   # 9:00 - 9:30
    (600, 1020)   # 10:00 - 17:00
]
# Tuesday: 9:00 to 10:30, 12:30 to 16:00, 16:30 to 17:00 
denise_tuesday_busy = [
    (540, 630),   # 9:00 - 10:30
    (750, 960),   # 12:30 - 16:00
    (990, 1020)   # 16:30 - 17:00
]

# Helper function to yield the non-overlap constraint.
def non_overlap(busy_start, busy_end):
    # The meeting interval [start, start+duration) should not overlap with [busy_start, busy_end)
    return Or(start + duration <= busy_start, start >= busy_end)

# Add busy constraints for Amy.
for b_start, b_end in amy_monday_busy:
    # For Monday (day==0)
    solver.add(Implies(day == 0, non_overlap(b_start, b_end)))
for b_start, b_end in amy_tuesday_busy:
    # For Tuesday (day==1)
    solver.add(Implies(day == 1, non_overlap(b_start, b_end)))

# Add busy constraints for Denise.
for b_start, b_end in denise_monday_busy:
    solver.add(Implies(day == 0, non_overlap(b_start, b_end)))
for b_start, b_end in denise_tuesday_busy:
    solver.add(Implies(day == 1, non_overlap(b_start, b_end)))

# Preference: Denise does not want to meet on Tuesday.
solver.add(day == 0)

# Search for a valid meeting time on Monday that satisfies all constraints.
found = False
result_start = None

for t in range(WORK_START, WORK_END - duration + 1):
    solver.push()
    solver.add(start == t)
    if solver.check() == sat:
        model = solver.model()
        result_start = model[start].as_long()
        result_day = "Monday" if model[day].as_long() == 0 else "Tuesday"
        found = True
        solver.pop()
        break
    solver.pop()

if found:
    meeting_end = result_start + duration
    sh, sm = divmod(result_start, 60)
    eh, em = divmod(meeting_end, 60)
    print(f"A valid meeting time is on {result_day} from {sh:02d}:{sm:02d} to {eh:02d}:{em:02d}.")
else:
    print("No valid meeting time could be found.")