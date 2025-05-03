from z3 import Solver, Int, Or, Implies, sat

# Meeting parameters.
duration = 30  # meeting duration in minutes
start = Int("start")  # start time in minutes since midnight
day = Int("day")      # day: 0 for Monday, 1 for Tuesday

# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
WORK_START = 540
WORK_END = 1020

solver = Solver()
solver.add(start >= WORK_START, start + duration <= WORK_END)
solver.add(Or(day == 0, day == 1))

# Participant busy schedules.

# Jesse's busy intervals.
# Monday: 13:00 to 13:30, 15:30 to 16:00 => (780,810), (930,960)
jesse_monday_busy = [
    (780, 810),
    (930, 960)
]
# Tuesday: 9:00 to 9:30, 13:00 to 13:30, 15:30 to 16:00, 16:30 to 17:00
jesse_tuesday_busy = [
    (540, 570),
    (780, 810),
    (930, 960),
    (990, 1020)
]

# Kenneth's busy intervals.
# Monday: 9:00 to 10:00, 11:30 to 14:00, 15:00 to 15:30
kenneth_monday_busy = [
    (540, 600),
    (690, 840),
    (900, 930)
]
# Tuesday: 9:00 to 12:30, 13:00 to 14:00, 16:00 to 16:30
kenneth_tuesday_busy = [
    (540, 750),
    (780, 840),
    (960, 990)
]

# Function to add non-overlap constraint between the meeting interval and a busy interval.
def add_non_overlap(busy_start, busy_end):
    # Meeting interval [start, start+duration) does not overlap busy interval [busy_start, busy_end)
    return Or(start + duration <= busy_start, start >= busy_end)

# Add Jesse's busy constraints.
for b_start, b_end in jesse_monday_busy:
    solver.add(Implies(day == 0, add_non_overlap(b_start, b_end)))
for b_start, b_end in jesse_tuesday_busy:
    solver.add(Implies(day == 1, add_non_overlap(b_start, b_end)))

# Add Kenneth's busy constraints.
for b_start, b_end in kenneth_monday_busy:
    solver.add(Implies(day == 0, add_non_overlap(b_start, b_end)))
for b_start, b_end in kenneth_tuesday_busy:
    solver.add(Implies(day == 1, add_non_overlap(b_start, b_end)))

# Preferences:
# Jesse would like to avoid more meetings on Tuesday.
# (Since a Monday meeting is possible, we force the meeting to be on Monday.)
solver.add(day == 0)

# Kenneth would like to avoid more meetings on Monday after 12:00.
# So if the meeting is on Monday, it should finish by 12:00 (720 minutes).
solver.add(Implies(day == 0, start + duration <= 720))

# Search for the earliest meeting time that satisfies the constraints.
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