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

# Constraint: Charles does not want to meet on Monday
solver.add(day == 1)

# Additional constraint from Charles: on Tuesday he does not want to meet after 15:30.
# That means the meeting must finish by 15:30 (i.e., 930 minutes).
solver.add(start + duration <= 930)

# Cheryl's busy schedule in minutes from midnight:
# Tuesday busy intervals:
#   9:30 to 10:00   -> (570, 600)
#   10:30 to 11:00  -> (630, 660)
#   11:30 to 13:00  -> (690, 780)
#   13:30 to 14:00  -> (810, 840)
#   15:00 to 15:30  -> (900, 930)
#   16:00 to 17:00  -> (960, 1020)
cheryl_tuesday_busy = [
    (570, 600),
    (630, 660),
    (690, 780),
    (810, 840),
    (900, 930),
    (960, 1020)
]

# Helper function: the meeting [start, start+duration) must not overlap a busy interval [busy_start, busy_end)
def non_overlap(busy_start, busy_end):
    return Or(start + duration <= busy_start, start >= busy_end)

# Add Cheryl's busy schedule constraints for Tuesday:
for b_start, b_end in cheryl_tuesday_busy:
    solver.add(Implies(day == 1, non_overlap(b_start, b_end)))

# Now, try to find a valid meeting time.
found = False
meeting_start = None
meeting_day = None

# We iterate over possible start times in 1 minute increments.
for t in range(WORK_START, WORK_END - duration + 1):
    solver.push()
    solver.add(start == t)
    if solver.check() == sat:
        model = solver.model()
        meeting_start = model[start].as_long()
        meeting_day = model[day].as_long()  # 1 for Tuesday (by our constraint)
        found = True
        solver.pop()
        break
    solver.pop()

if found:
    meeting_end = meeting_start + duration
    s_hour, s_min = divmod(meeting_start, 60)
    e_hour, e_min = divmod(meeting_end, 60)
    # day_str is predetermined since day==1 always
    day_str = "Tuesday"
    print(f"A valid meeting time is on {day_str} from {s_hour:02d}:{s_min:02d} to {e_hour:02d}:{e_min:02d}.")
else:
    print("No valid meeting time could be found.")