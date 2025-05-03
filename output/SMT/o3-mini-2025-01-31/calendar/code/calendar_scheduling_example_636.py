from z3 import Solver, Int, Or, Implies, sat

# Meeting parameters:
duration = 30  # meeting duration is 30 minutes
start = Int("start")  # meeting start time in minutes from midnight
day = Int("day")      # day: 0 for Monday, 1 for Tuesday

# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
WORK_START = 540
WORK_END = 1020

solver = Solver()
solver.add(start >= WORK_START, start + duration <= WORK_END)
solver.add(Or(day == 0, day == 1))

# Participant preferences:
# Madison does not want to meet on Monday, so the meeting must be on Tuesday.
solver.add(day == 1)
# Lauren would like to avoid more meetings on Tuesday after 10:30.
# That means the meeting must finish by 10:30 (630 minutes).
solver.add(start + duration <= 630)

# Busy schedules (times in minutes from midnight):
# Tuesday busy schedules for Madison:
#   9:00 to 9:30   -> (540, 570)
#   10:30 to 11:00 -> (630, 660)
#   12:00 to 12:30 -> (720, 750)
#   13:30 to 14:30 -> (810, 870)
#   16:30 to 17:00 -> (990, 1020)
madison_tuesday_busy = [
    (540, 570),
    (630, 660),
    (720, 750),
    (810, 870),
    (990, 1020)
]

# Tuesday busy schedules for Lauren:
#   9:00 to 9:30   -> (540, 570)
#   10:00 to 10:30 -> (600, 630)
#   12:00 to 13:30 -> (720, 810)
#   14:30 to 15:00 -> (870, 900)
#   16:30 to 17:00 -> (990, 1020)
lauren_tuesday_busy = [
    (540, 570),
    (600, 630),
    (720, 810),
    (870, 900),
    (990, 1020)
]

# Helper function: meeting interval [start, start+duration) must not overlap busy interval [busy_start, busy_end)
def non_overlap(busy_start, busy_end):
    return Or(start + duration <= busy_start, start >= busy_end)

# Add busy constraints for Madison on Tuesday:
for b_start, b_end in madison_tuesday_busy:
    solver.add(Implies(day == 1, non_overlap(b_start, b_end)))

# Add busy constraints for Lauren on Tuesday:
for b_start, b_end in lauren_tuesday_busy:
    solver.add(Implies(day == 1, non_overlap(b_start, b_end)))

# Search for a valid meeting time by iterating over possible start times within work hours.
found = False
meeting_start = None
meeting_day = None

for t in range(WORK_START, WORK_END - duration + 1):
    solver.push()
    solver.add(start == t)
    if solver.check() == sat:
        model = solver.model()
        meeting_start = model[start].as_long()
        meeting_day = model[day].as_long()  # (will be 1 for Tuesday)
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