from z3 import Solver, Int, Or, Implies, sat

# Meeting parameters
duration = 30  # half an hour meeting duration in minutes
start = Int("start")  # meeting start time in minutes since midnight
day = Int("day")      # day: 0 for Monday, 1 for Tuesday

# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
WORK_START = 540
WORK_END = 1020

# Create a Z3 solver and add the basic constraints:
# Meeting must be within work hours.
solver = Solver()
solver.add(start >= WORK_START, start + duration <= WORK_END)
# day is 0 (Monday) or 1 (Tuesday)
solver.add(Or(day == 0, day == 1))

# Busy intervals for Sarah and Terry, expressed in minutes since midnight.

# Sarah's busy schedule:
# Monday:
#   9:00 to 10:00 -> (540, 600)
#   11:30 to 12:00 -> (690, 720)
#   14:30 to 15:30 -> (870, 930)
sarah_monday_busy = [(540, 600), (690, 720), (870, 930)]
# Tuesday:
#   9:00 to 9:30 -> (540, 570)
#   11:30 to 12:00 -> (690, 720)
#   15:00 to 15:30 -> (900, 930)
sarah_tuesday_busy = [(540, 570), (690, 720), (900, 930)]

# Terry's busy schedule:
# Monday:
#   10:00 to 10:30 -> (600, 630)
#   11:30 to 14:00 -> (690, 840)
#   16:00 to 17:00 -> (960, 1020)
terry_monday_busy = [(600, 630), (690, 840), (960, 1020)]
# Tuesday:
#   9:00 to 9:30 -> (540, 570)
#   10:00 to 12:30 -> (600, 750)
#   13:00 to 17:00 -> (780, 1020)
terry_tuesday_busy = [(540, 570), (600, 750), (780, 1020)]

# Helper function: The meeting interval [start, start+duration)
# must not overlap with a busy interval [busy_start, busy_end)
def non_overlap(busy_start, busy_end):
    return Or(start + duration <= busy_start, start >= busy_end)

# Add Sarah's busy constraints (if day matches)
for b_start, b_end in sarah_monday_busy:
    solver.add(Implies(day == 0, non_overlap(b_start, b_end)))
for b_start, b_end in sarah_tuesday_busy:
    solver.add(Implies(day == 1, non_overlap(b_start, b_end)))

# Add Terry's busy constraints (if day matches)
for b_start, b_end in terry_monday_busy:
    solver.add(Implies(day == 0, non_overlap(b_start, b_end)))
for b_start, b_end in terry_tuesday_busy:
    solver.add(Implies(day == 1, non_overlap(b_start, b_end)))

# Preference: Sarah would like to avoid more meetings on Monday.
# So we try to schedule on Tuesday first, if a valid slot is available.
# Also, we want the earliest available time.

found = False
meeting_start = None
meeting_day = None

# Try Tuesday first (day == 1)
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

# If no valid slot on Tuesday, then check Monday.
if not found:
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

if found:
    meeting_end = meeting_start + duration
    start_hour, start_min = divmod(meeting_start, 60)
    end_hour, end_min = divmod(meeting_end, 60)
    day_str = "Monday" if meeting_day == 0 else "Tuesday"
    print(f"A valid meeting time is on {day_str} from {start_hour:02d}:{start_min:02d} to {end_hour:02d}:{end_min:02d}.")
else:
    print("No valid meeting time could be found.")