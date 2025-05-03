from z3 import Solver, Int, Or, Implies, sat

# Meeting parameters:
duration = 30  # meeting duration in minutes
start = Int("start")  # meeting start time in minutes from midnight
day = Int("day")      # day: 0 for Monday, 1 for Tuesday

# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
WORK_START = 540
WORK_END = 1020

solver = Solver()
solver.add(start >= WORK_START, start + duration <= WORK_END)
solver.add(Or(day == 0, day == 1))

# Participant preferences:
# Cheryl would rather not meet on Tuesday, so force the meeting to be on Monday.
solver.add(day == 0)

# Busy schedules (times in minutes from midnight):

# Cheryl's busy times on Monday:
#   9:00 to 10:30 -> (540, 630)
#   11:00 to 11:30 -> (660, 690)
#   14:00 to 14:30 -> (840, 870)
#   16:00 to 16:30 -> (960, 990)
cheryl_monday_busy = [
    (540, 630),
    (660, 690),
    (840, 870),
    (960, 990)
]

# Janice's busy times on Monday:
#   9:00 to 11:30  -> (540, 690)
#   12:00 to 14:00 -> (720, 840)
#   14:30 to 17:00 -> (870, 1020)
janice_monday_busy = [
    (540, 690),
    (720, 840),
    (870, 1020)
]

# Helper function: meeting interval [start, start+duration) must not overlap busy interval [bstart, bend)
def non_overlap(bstart, bend):
    return Or(start + duration <= bstart, start >= bend)

# Add busy constraints for Cheryl on Monday:
for b_start, b_end in cheryl_monday_busy:
    solver.add(Implies(day == 0, non_overlap(b_start, b_end)))

# Add busy constraints for Janice on Monday:
for b_start, b_end in janice_monday_busy:
    solver.add(Implies(day == 0, non_overlap(b_start, b_end)))

# Try to find a valid meeting time by iterating through possible start times.
found = False
meeting_start = None
meeting_day = None

for t in range(WORK_START, WORK_END - duration + 1):
    solver.push()
    solver.add(start == t)
    if solver.check() == sat:
        model = solver.model()
        meeting_start = model[start].as_long()
        meeting_day = model[day].as_long()  # should be 0 (Monday)
        found = True
        solver.pop()
        break
    solver.pop()

if found:
    meeting_end = meeting_start + duration
    s_hour, s_min = divmod(meeting_start, 60)
    e_hour, e_min = divmod(meeting_end, 60)
    day_str = "Monday" if meeting_day == 0 else "Tuesday"
    print(f"A valid meeting time is on {day_str} from {s_hour:02d}:{s_min:02d} to {e_hour:02d}:{e_min:02d}.")
else:
    print("No valid meeting time could be found.")