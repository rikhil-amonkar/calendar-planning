from z3 import Solver, Int, Or, Implies, sat

# Meeting parameters
duration = 30  # meeting duration in minutes
start = Int("start")  # meeting start time in minutes since midnight
day = Int("day")      # day: 0 for Monday, 1 for Tuesday

# Work hours: 9:00 (540) to 17:00 (1020)
WORK_START = 540
WORK_END = 1020

# Create the Z3 solver and add basic constraints
solver = Solver()
solver.add(start >= WORK_START, start + duration <= WORK_END)
solver.add(Or(day == 0, day == 1))

# Maria's constraint: Maria cannot meet on Monday after 15:00.
# This means if the meeting is on Monday (day==0), the meeting must finish by 15:00 (900 minutes)
solver.add(Implies(day == 0, start + duration <= 900))

# Danielle's busy schedule (in minutes):
# Monday busy intervals:
#   9:30 to 10:00 -> (570, 600)
#   11:00 to 12:00 -> (660, 720)
#   13:00 to 13:30 -> (780, 810)
#   14:30 to 15:00 -> (870, 900)
#   15:30 to 16:00 -> (930, 960)
#   16:30 to 17:00 -> (990, 1020)
danielle_monday_busy = [
    (570, 600),
    (660, 720),
    (780, 810),
    (870, 900),
    (930, 960),
    (990, 1020)
]
# Tuesday busy intervals:
#   9:00 to 11:00  -> (540, 660)
#   11:30 to 17:00 -> (690, 1020)
danielle_tuesday_busy = [
    (540, 660),
    (690, 1020)
]

# Define a helper function to express that the meeting interval does not overlap a busy interval.
def non_overlap(busy_start, busy_end):
    # Meeting [start, start+duration) must either finish before the busy interval starts,
    # or start after the busy interval ends.
    return Or(start + duration <= busy_start, start >= busy_end)

# Add Danielle's busy constraints for Monday.
for b_start, b_end in danielle_monday_busy:
    solver.add(Implies(day == 0, non_overlap(b_start, b_end)))

# Add Danielle's busy constraints for Tuesday.
for b_start, b_end in danielle_tuesday_busy:
    solver.add(Implies(day == 1, non_overlap(b_start, b_end)))

# Preference: Danielle would like to avoid more meetings on Tuesday.
# So we try to schedule on Monday first, if possible.

found = False
meeting_start = None
meeting_day = None

# Try Monday first
for t in range(WORK_START, WORK_END - duration + 1):
    solver.push()
    solver.add(start == t, day == 0)  # force Monday
    if solver.check() == sat:
        model = solver.model()
        meeting_start = model[start].as_long()
        meeting_day = model[day].as_long()  # should be 0 for Monday
        found = True
        solver.pop()
        break
    solver.pop()

# If no valid slot is found on Monday, try Tuesday.
if not found:
    for t in range(WORK_START, WORK_END - duration + 1):
        solver.push()
        solver.add(start == t, day == 1)  # force Tuesday
        if solver.check() == sat:
            model = solver.model()
            meeting_start = model[start].as_long()
            meeting_day = model[day].as_long()  # should be 1 for Tuesday
            found = True
            solver.pop()
            break
        solver.pop()

if found:
    meeting_end = meeting_start + duration
    start_hour, start_min = divmod(meeting_start, 60)
    end_hour, end_min = divmod(meeting_end, 60)
    day_str = "Monday" if meeting_day == 0 else "Tuesday"
    print(f"A valid meeting time is on {day_str} from {start_hour:02d}:{start_min:02d} to {end_hour:02d}:{end_min:02d}.")
else:
    print("No valid meeting time could be found.")