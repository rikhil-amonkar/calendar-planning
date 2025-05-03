from z3 import Solver, Int, Or, Implies, sat

# Meeting parameters
duration = 60  # meeting duration in minutes (1 hour)
start = Int("start")  # meeting start time in minutes from midnight
day = Int("day")      # day: 0 for Monday, 1 for Tuesday

# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
WORK_START = 540
WORK_END = 1020

# Create the Z3 solver and add basic constraints: meeting must finish by WORK_END.
solver = Solver()
solver.add(start >= WORK_START, start + duration <= WORK_END)
solver.add(Or(day == 0, day == 1))

# Busy schedules in minutes from midnight

# Alexander's busy schedule:
# Monday:
#   9:30 to 10:00 -> (570, 600)
#   11:30 to 12:00 -> (690, 720)
#   16:30 to 17:00 -> (990, 1020)
alex_monday_busy = [(570, 600), (690, 720), (990, 1020)]
# Tuesday:
#   9:00 to 9:30   -> (540, 570)
#   11:00 to 12:00 -> (660, 720)
#   14:30 to 15:00 -> (870, 900)
#   16:30 to 17:00 -> (990, 1020)
alex_tuesday_busy = [(540, 570), (660, 720), (870, 900), (990, 1020)]

# Marilyn's busy schedule:
# Monday:
#   9:00 to 10:00   -> (540, 600)
#   11:00 to 12:00  -> (660, 720)
#   12:30 to 13:00  -> (750, 780)
#   13:30 to 14:00  -> (810, 840)
#   14:30 to 17:00  -> (870, 1020)
marilyn_monday_busy = [(540, 600), (660, 720), (750, 780), (810, 840), (870, 1020)]
# Tuesday:
#   9:00 to 9:30   -> (540, 570)
#   10:00 to 13:30  -> (600, 810)
#   14:00 to 15:00  -> (840, 900)
#   15:30 to 17:00  -> (930, 1020)
marilyn_tuesday_busy = [(540, 570), (600, 810), (840, 900), (930, 1020)]

# Define a helper function that ensures the meeting interval [start, start+duration)
# does not overlap with a busy interval [busy_start, busy_end)
def non_overlap(busy_start, busy_end):
    return Or(start + duration <= busy_start, start >= busy_end)

# Add constraints for Alexander's busy intervals using an implication for each day.
for b_start, b_end in alex_monday_busy:
    solver.add(Implies(day == 0, non_overlap(b_start, b_end)))
for b_start, b_end in alex_tuesday_busy:
    solver.add(Implies(day == 1, non_overlap(b_start, b_end)))

# Add constraints for Marilyn's busy intervals.
for b_start, b_end in marilyn_monday_busy:
    solver.add(Implies(day == 0, non_overlap(b_start, b_end)))
for b_start, b_end in marilyn_tuesday_busy:
    solver.add(Implies(day == 1, non_overlap(b_start, b_end)))

# Search for the earliest possible meeting time that satisfies all constraints.
found = False
meeting_start = None
meeting_day = None

# We'll iterate over possible start times within work hours.
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
    start_hour, start_min = divmod(meeting_start, 60)
    end_hour, end_min = divmod(meeting_end, 60)
    day_str = "Monday" if meeting_day == 0 else "Tuesday"
    print(f"A valid meeting time is on {day_str} from {start_hour:02d}:{start_min:02d} to {end_hour:02d}:{end_min:02d}.")
else:
    print("No valid meeting time could be found.")