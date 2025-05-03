from z3 import Solver, Int, Or, Implies, sat

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters.
duration = 30  # meeting duration in minutes (half an hour)
start = Int("start")  # meeting start time (in minutes since midnight)
day = Int("day")      # 0 represents Monday, 1 represents Tuesday

# The meeting must be scheduled on Monday (0) or Tuesday (1).
solver.add(Or(day == 0, day == 1))

# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
solver.add(start >= 540, start + duration <= 1020)

# Define a helper that, given a list of busy intervals, 
# adds a constraint ensuring the meeting does not overlap each interval when it is on a given day.
def add_busy_for_day(solver, current_day, busy_intervals):
    for b_start, b_end in busy_intervals:
        # When we are on the target day, ensure that the meeting interval [start, start+duration)
        # does not overlap the busy interval [b_start, b_end)
        solver.add(Implies(day == current_day, Or(start + duration <= b_start, start >= b_end)))

# Busy intervals for Mark:
# Monday busy intervals: 
#   9:00 to 9:30 -> [540,570)
#   10:00 to 10:30 -> [600,630)
#   12:30 to 13:00 -> [750,780)
#   16:00 to 16:30 -> [960,990)
mark_monday_busy = [
    (540, 570),
    (600, 630),
    (750, 780),
    (960, 990)
]
# Tuesday busy intervals:
#   9:00 to 10:00 -> [540,600)
#   12:00 to 12:30 -> [720,750)
#   14:00 to 14:30 -> [840,870)
mark_tuesday_busy = [
    (540, 600),
    (720, 750),
    (840, 870)
]

# Busy intervals for Marie:
# Monday busy intervals:
#   9:30 to 11:30 -> [570,690)
#   12:00 to 17:00 -> [720,1020)
marie_monday_busy = [
    (570, 690),
    (720, 1020)
]
# Tuesday busy intervals:
#   9:00 to 17:00 -> [540,1020)
marie_tuesday_busy = [
    (540, 1020)
]

# Add busy constraints for Monday (day == 0).
add_busy_for_day(solver, 0, mark_monday_busy)
add_busy_for_day(solver, 0, marie_monday_busy)

# Add busy constraints for Tuesday (day == 1).
add_busy_for_day(solver, 1, mark_tuesday_busy)
add_busy_for_day(solver, 1, marie_tuesday_busy)

# We want the earliest possible meeting time.
# We'll iterate over days in order (Monday first, then Tuesday) and for each day, 
# check possible start times within the work hours.
found = False
for current_day in [0, 1]:
    for t in range(540, 1020 - duration + 1):
        solver.push()
        solver.add(day == current_day, start == t)
        if solver.check() == sat:
            meeting_start = t
            meeting_end = t + duration
            meeting_day = "Monday" if current_day == 0 else "Tuesday"
            sh, sm = divmod(meeting_start, 60)
            eh, em = divmod(meeting_end, 60)
            print(f"A valid meeting time is on {meeting_day} from {sh:02d}:{sm:02d} to {eh:02d}:{em:02d}.")
            found = True
            solver.pop()
            break
        solver.pop()
    if found:
        break

if not found:
    print("No valid meeting time could be found.")