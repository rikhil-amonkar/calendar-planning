from z3 import Solver, Int, Or, Implies, sat

# Meeting parameters.
duration = 30  # meeting duration in minutes
start = Int("start")  # start time in minutes since midnight
day = Int("day")      # day: 0 for Monday, 1 for Tuesday

# Work hours: 9:00 (540 min) to 17:00 (1020 min)
WORK_START = 540
WORK_END = 1020

solver = Solver()
solver.add(start >= WORK_START, start + duration <= WORK_END)
solver.add(Or(day == 0, day == 1))

# Stephanie's busy intervals:
# Monday: 9:30 to 10:00, 12:00 to 12:30, 14:00 to 15:00
# (No busy intervals provided for Tuesday)
steph_monday_busy = [
    (570, 600),  # 9:30 - 10:00
    (720, 750),  # 12:00 - 12:30
    (840, 900)   # 14:00 - 15:00
]

# Billy's busy intervals:
# Monday: 9:00 to 17:00
# Tuesday: 9:30 to 12:30, 13:00 to 17:00
billy_monday_busy = [
    (540, 1020)  # 9:00 - 17:00, entire day busy on Monday
]
billy_tuesday_busy = [
    (570, 750),  # 9:30 - 12:30
    (780, 1020)  # 13:00 - 17:00
]

# Function to add non-overlap constraints.
def add_non_overlap(solver, interval):
    busy_start, busy_end = interval
    solver.add(Or(start + duration <= busy_start, start >= busy_end))

# Add Stephanie's constraints:
for interval in steph_monday_busy:
    solver.add(Implies(day == 0, Or(start + duration <= interval[0], start >= interval[1])))

# Add Billy's constraints:
for interval in billy_monday_busy:
    solver.add(Implies(day == 0, Or(start + duration <= interval[0], start >= interval[1])))
for interval in billy_tuesday_busy:
    solver.add(Implies(day == 1, Or(start + duration <= interval[0], start >= interval[1])))

# Additional preference:
# Billy would rather not meet on Tuesday before 11:30 (11:30 = 690 minutes)
solver.add(Implies(day == 1, start >= 690))

# Given that Billy is busy all day on Monday, the meeting will have to be on Tuesday.
# We search for the earliest meeting start time that satisfies all constraints.
found = False
result_start = None
result_day = None

for t in range(WORK_START, WORK_END - duration + 1):
    solver.push()
    solver.add(start == t)
    if solver.check() == sat:
        model = solver.model()
        result_start = model[start].as_long()
        d = model[day].as_long()
        result_day = "Monday" if d == 0 else "Tuesday"
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