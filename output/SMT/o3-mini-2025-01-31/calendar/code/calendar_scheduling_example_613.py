from z3 import Solver, Int, Or, Implies, sat

# Meeting parameters
duration = 60  # meeting duration in minutes
start = Int("start")  # meeting start time in minutes since midnight
day = Int("day")      # day: 0 for Monday, 1 for Tuesday

# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
WORK_START = 540
WORK_END = 1020

solver = Solver()
solver.add(start >= WORK_START, start + duration <= WORK_END)
solver.add(Or(day == 0, day == 1))

# Sharon's busy schedule:
# Monday busy intervals (in minutes):
#   10:00 to 10:30 -> (600, 630)
#   11:30 to 12:00 -> (690, 720)
#   13:00 to 15:00 -> (780, 900)
sharon_monday_busy = [
    (600, 630),
    (690, 720),
    (780, 900)
]
# Tuesday busy intervals:
#   9:00 to 10:00   -> (540, 600)
#   10:30 to 11:00  -> (630, 660)
#   14:00 to 14:30  -> (840, 870)
#   16:00 to 17:00  -> (960, 1020)
sharon_tuesday_busy = [
    (540, 600),
    (630, 660),
    (840, 870),
    (960, 1020)
]

# Logan's busy schedule:
# Monday busy intervals:
#   9:00 to 9:30   -> (540, 570)
#   10:00 to 12:00 -> (600, 720)
#   12:30 to 14:30 -> (750, 870)
#   15:30 to 17:00 -> (930, 1020)
logan_monday_busy = [
    (540, 570),
    (600, 720),
    (750, 870),
    (930, 1020)
]
# Tuesday busy intervals:
#   9:00 to 14:30  -> (540, 870)
#   15:30 to 17:00 -> (930, 1020)
logan_tuesday_busy = [
    (540, 870),
    (930, 1020)
]

# Helper function: ensures that meeting interval [start, start+duration)
# does not overlap with a busy interval [busy_start, busy_end)
def non_overlap(busy_start, busy_end):
    return Or(start + duration <= busy_start, start >= busy_end)

# Add Sharon's busy constraints for Monday and Tuesday
for b_start, b_end in sharon_monday_busy:
    solver.add(Implies(day == 0, non_overlap(b_start, b_end)))
for b_start, b_end in sharon_tuesday_busy:
    solver.add(Implies(day == 1, non_overlap(b_start, b_end)))

# Add Logan's busy constraints for Monday and Tuesday
for b_start, b_end in logan_monday_busy:
    solver.add(Implies(day == 0, non_overlap(b_start, b_end)))
for b_start, b_end in logan_tuesday_busy:
    solver.add(Implies(day == 1, non_overlap(b_start, b_end)))

# We want the meeting at the earliest availability.
# We'll iterate over candidate start times from WORK_START to WORK_END-duration.
found = False
meeting_start = None
meeting_day = None

for t in range(WORK_START, WORK_END - duration + 1):
    solver.push()
    solver.add(start == t)
    if solver.check() == sat:
        model = solver.model()
        meeting_start = model[start].as_long()
        meeting_day = model[day].as_long()
        found = True
        solver.pop()
        break
    solver.pop()

if found:
    meeting_end = meeting_start + duration
    sh, sm = divmod(meeting_start, 60)
    eh, em = divmod(meeting_end, 60)
    day_str = "Monday" if meeting_day == 0 else "Tuesday"
    print(f"A valid meeting time is on {day_str} from {sh:02d}:{sm:02d} to {eh:02d}:{em:02d}.")
else:
    print("No valid meeting time could be found.")