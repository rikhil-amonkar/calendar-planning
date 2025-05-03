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

# Participants' preferences:
# Emily cannot meet on Monday, so the meeting must be on Tuesday.
solver.add(day == 1)
# Jesse does not want to meet on Tuesday after 10:00,
# so on Tuesday the meeting must finish by 10:00 (600 minutes).
solver.add(Implies(day == 1, start + duration <= 600))

# Busy schedules (in minutes from midnight):

# Jesse's busy times:
# Monday:
#   16:00 to 16:30 -> (960, 990)
# Tuesday:
#   14:00 to 14:30 -> (840, 870)
jesse_monday_busy = [
    (960, 990)
]
jesse_tuesday_busy = [
    (840, 870)
]

# Emily's busy times:
# Monday:
#   9:00 to 14:30 -> (540, 870)
#   15:00 to 15:30 -> (900, 930)
#   16:00 to 17:00 -> (960, 1020)
emily_monday_busy = [
    (540, 870),
    (900, 930),
    (960, 1020)
]
# Tuesday:
#   9:30 to 15:00 -> (570, 900)
#   15:30 to 17:00 -> (930, 1020)
emily_tuesday_busy = [
    (570, 900),
    (930, 1020)
]

# Helper function: meeting [start, start+duration) must not overlap busy interval [bstart, bend)
def non_overlap(bstart, bend):
    return Or(start + duration <= bstart, start >= bend)

# Add Jesse's busy constraints:
for bstart, bend in jesse_monday_busy:
    solver.add(Implies(day == 0, non_overlap(bstart, bend)))
for bstart, bend in jesse_tuesday_busy:
    solver.add(Implies(day == 1, non_overlap(bstart, bend)))

# Add Emily's busy constraints:
for bstart, bend in emily_monday_busy:
    solver.add(Implies(day == 0, non_overlap(bstart, bend)))
for bstart, bend in emily_tuesday_busy:
    solver.add(Implies(day == 1, non_overlap(bstart, bend)))

# Search for a valid meeting time by iterating minute-by-minute.
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
    s_hour, s_min = divmod(meeting_start, 60)
    e_hour, e_min = divmod(meeting_end, 60)
    day_str = "Monday" if meeting_day == 0 else "Tuesday"
    print(f"A valid meeting time is on {day_str} from {s_hour:02d}:{s_min:02d} to {e_hour:02d}:{e_min:02d}.")
else:
    print("No valid meeting time could be found.")