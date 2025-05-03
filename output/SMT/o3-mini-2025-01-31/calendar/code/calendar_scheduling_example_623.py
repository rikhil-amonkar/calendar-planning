from z3 import Solver, Int, Or, Implies, sat

# Meeting parameters:
duration = 30  # meeting duration in minutes (half an hour)
start = Int("start")  # start time (in minutes after midnight)
day = Int("day")      # day: 0 for Monday, 1 for Tuesday

# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
WORK_START = 540
WORK_END = 1020

solver = Solver()
solver.add(start >= WORK_START, start + duration <= WORK_END)
solver.add(Or(day == 0, day == 1))

# Define the busy intervals (in minutes) for Melissa and James:

# Melissa's busy schedule:
# Monday:
#   9:00 to 9:30   -> (540, 570)
#   12:00 to 12:30 -> (720, 750)
#   14:00 to 14:30 -> (840, 870)
#   16:00 to 16:30 -> (960, 990)
melissa_monday_busy = [(540, 570), (720, 750), (840, 870), (960, 990)]
# Tuesday:
#   9:00 to 9:30   -> (540, 570)
#   10:00 to 10:30 -> (600, 630)
#   11:00 to 11:30 -> (660, 690)
#   12:30 to 14:30 -> (750, 870)
#   15:30 to 16:00 -> (930, 960)
melissa_tuesday_busy = [(540, 570), (600, 630), (660, 690), (750, 870), (930, 960)]

# James's busy schedule:
# Monday:
#   9:30 to 11:30  -> (570, 690)
#   12:00 to 14:00  -> (720, 840)
#   14:30 to 15:30  -> (870, 930)
#   16:00 to 16:30  -> (960, 990)
james_monday_busy = [(570, 690), (720, 840), (870, 930), (960, 990)]
# Tuesday:
#   9:30 to 10:00  -> (570, 600)
#   10:30 to 13:00  -> (630, 780)
#   13:30 to 17:00  -> (810, 1020)
james_tuesday_busy = [(570, 600), (630, 780), (810, 1020)]

# Helper function to ensure meeting [start, start+duration) does not overlap a busy interval.
def non_overlap(busy_start, busy_end):
    return Or(start + duration <= busy_start, start >= busy_end)

# Add Melissa's busy schedule constraints:
for b_start, b_end in melissa_monday_busy:
    solver.add(Implies(day == 0, non_overlap(b_start, b_end)))
for b_start, b_end in melissa_tuesday_busy:
    solver.add(Implies(day == 1, non_overlap(b_start, b_end)))

# Add James's busy schedule constraints:
for b_start, b_end in james_monday_busy:
    solver.add(Implies(day == 0, non_overlap(b_start, b_end)))
for b_start, b_end in james_tuesday_busy:
    solver.add(Implies(day == 1, non_overlap(b_start, b_end)))

# Preference: Melissa would rather not meet on Monday after 16:30.
# That is, if the meeting is on Monday (day == 0), we require the meeting to finish at or before 16:30 (990 minutes).
solver.add(Implies(day == 0, start + duration <= 990))

# Find the earliest available meeting time.
found = False
meeting_start = None
meeting_day = None

for t in range(WORK_START, WORK_END - duration + 1):
    solver.push()
    solver.add(start == t)
    if solver.check() == sat:
        model = solver.model()
        meeting_start = model[start].as_long()
        meeting_day = model[day].as_long()  # 0 for Monday, 1 for Tuesday
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