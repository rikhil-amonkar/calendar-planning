from z3 import Solver, Int, Or, sat

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters:
# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
duration = 60  # meeting duration is 1 hour
start = Int("start")  # Meeting start time in minutes since midnight.

# The meeting must finish by 17:00.
solver.add(start >= 540, start + duration <= 1020)

# Helper function to add non-overlap constraints for busy intervals.
def add_busy_constraints(solver, busy_intervals):
    for b_start, b_end in busy_intervals:
        # The meeting [start, start+duration) must either finish before the busy interval
        # starts, or start after the busy interval ends.
        solver.add(Or(start + duration <= b_start, start >= b_end))

# Participant schedules:

# Evelyn is free the entire day -> no constraints.

# Joshua is busy on Monday during:
# 11:00 to 12:30 -> [660,750)
# 13:30 to 14:30 -> [810,870)
# 16:30 to 17:00 -> [990,1020)
joshua_busy = [(660, 750), (810, 870), (990, 1020)]
add_busy_constraints(solver, joshua_busy)

# Kevin is free the entire day -> no constraints.

# Gerald is free the entire day -> no constraints.

# Jerry is busy on Monday during:
# 9:00 to 9:30   -> [540,570)
# 10:30 to 12:00 -> [630,720)
# 12:30 to 13:00 -> [750,780)
# 13:30 to 14:00 -> [810,840)
# 14:30 to 15:00 -> [870,900)
# 15:30 to 16:00 -> [930,960)
jerry_busy = [(540, 570), (630, 720), (750, 780), (810, 840), (870, 900), (930, 960)]
add_busy_constraints(solver, jerry_busy)

# Jesse is busy on Monday during:
# 9:00 to 9:30   -> [540,570)
# 10:30 to 12:00 -> [630,720)
# 12:30 to 13:00 -> [750,780)
# 14:30 to 15:00 -> [870,900)
# 15:30 to 16:30 -> [930,990)
jesse_busy = [(540, 570), (630, 720), (750, 780), (870, 900), (930, 990)]
add_busy_constraints(solver, jesse_busy)

# Kenneth is busy on Monday during:
# 10:30 to 12:30 -> [630,750)
# 13:30 to 14:00 -> [810,840)
# 14:30 to 15:00 -> [870,900)
# 15:30 to 16:00 -> [930,960)
# 16:30 to 17:00 -> [990,1020)
kenneth_busy = [(630, 750), (810, 840), (870, 900), (930, 960), (990, 1020)]
add_busy_constraints(solver, kenneth_busy)

# Search for the earliest meeting time that satisfies all constraints.
found = False
for t in range(540, 1020 - duration + 1):  # meeting must start at a time so that t+60 <=1020
    solver.push()
    solver.add(start == t)
    if solver.check() == sat:
        meeting_start = t
        meeting_end = t + duration
        start_hour, start_min = divmod(meeting_start, 60)
        end_hour, end_min = divmod(meeting_end, 60)
        print(f"A valid meeting time is from {start_hour:02d}:{start_min:02d} to {end_hour:02d}:{end_min:02d}.")
        found = True
        solver.pop()
        break
    solver.pop()

if not found:
    print("No valid meeting time could be found.")