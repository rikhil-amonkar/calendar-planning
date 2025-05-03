from z3 import Solver, Int, Or, Implies, sat

# Meeting parameters.
duration = 60  # meeting duration in minutes (1 hour)
start = Int("start")  # meeting start time in minutes since midnight
day = Int("day")      # day of the meeting (0 for Monday, 1 for Tuesday)

# Work hours: from 9:00 (540 minutes) to 17:00 (1020 minutes)
WORK_START = 540
WORK_END = 1020
solver = Solver()
solver.add(start >= WORK_START, start + duration <= WORK_END)
solver.add(Or(day == 0, day == 1))

# Anna's busy intervals.
anna_monday_busy = [
    (540, 570),  # 9:00 to 9:30
    (660, 720),  # 11:00 to 12:00
    (840, 870),  # 14:00 to 14:30
    (900, 930)   # 15:00 to 15:30
]
anna_tuesday_busy = [
    (540, 600),  # 9:00 to 10:00
    (750, 810),  # 12:30 to 13:30
    (990, 1020)  # 16:30 to 17:00
]

# Margaret's busy intervals.
margaret_monday_busy = [
    (540, 840),  # 9:00 to 14:00
    (870, 1020)  # 14:30 to 17:00
]
margaret_tuesday_busy = [
    (540, 630),   # 9:00 to 10:30
    (690, 720),   # 11:30 to 12:00
    (750, 870),   # 12:30 to 14:30
    (930, 1020)   # 15:30 to 17:00
]

# Function to add non-overlap constraint for a busy interval.
def add_non_overlap(solver, busy_start, busy_end):
    # Meeting interval [start, start+duration) must not overlap busy interval [busy_start, busy_end)
    solver.add(Or(start + duration <= busy_start, start >= busy_end))

# Add Anna's busy schedule constraints.
for b_start, b_end in anna_monday_busy:
    solver.add(Implies(day == 0, Or(start + duration <= b_start, start >= b_end)))
for b_start, b_end in anna_tuesday_busy:
    solver.add(Implies(day == 1, Or(start + duration <= b_start, start >= b_end)))

# Add Margaret's busy schedule constraints.
for b_start, b_end in margaret_monday_busy:
    solver.add(Implies(day == 0, Or(start + duration <= b_start, start >= b_end)))
for b_start, b_end in margaret_tuesday_busy:
    solver.add(Implies(day == 1, Or(start + duration <= b_start, start >= b_end)))

# Additional preference: Anna would rather not meet on Tuesday before 14:30.
# If the meeting is on Tuesday (day == 1) then the meeting start must be >= 14:30 (870 minutes).
solver.add(Implies(day == 1, start >= 870))

# Now, search for the earliest possible meeting start time.
found = False
result_day = None
result_start = None

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