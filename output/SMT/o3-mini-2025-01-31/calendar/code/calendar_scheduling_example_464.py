from z3 import Solver, Int, Or, sat

# Create a new Z3 solver instance.
solver = Solver()

# Meeting parameters:
# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
# Meeting duration: 30 minutes.
duration = 30
start = Int("start")  # meeting start time in minutes since midnight

# Ensure the meeting is within work hours.
solver.add(start >= 540, start + duration <= 1020)

# Helper function to add non-overlap constraints for busy intervals.
def add_busy_constraints(solver, busy_intervals):
    for busy_start, busy_end in busy_intervals:
        # The meeting [start, start+duration) must either finish
        # before the busy interval starts or start after it ends.
        solver.add(Or(start + duration <= busy_start, start >= busy_end))

# Rachel's busy intervals:
# 10:30 to 11:30 -> [630, 690)
rachel_busy = [(630, 690)]
add_busy_constraints(solver, rachel_busy)

# Henry's busy intervals:
# 10:30 to 11:00 -> [630, 660)
# 12:00 to 12:30 -> [720, 750)
henry_busy = [(630, 660), (720, 750)]
add_busy_constraints(solver, henry_busy)

# Jesse's busy intervals:
# 11:30 to 12:00 -> [690, 720)
# 12:30 to 14:30 -> [750, 870)
# 15:30 to 16:00 -> [930, 960)
jesse_busy = [(690, 720), (750, 870), (930, 960)]
add_busy_constraints(solver, jesse_busy)

# Albert's busy intervals:
# 10:30 to 12:00 -> [630, 720)
# 16:00 to 16:30 -> [960, 990)
albert_busy = [(630, 720), (960, 990)]
add_busy_constraints(solver, albert_busy)

# Ashley's busy intervals:
# 9:00 to 9:30   -> [540, 570)
# 10:30 to 12:30 -> [630, 750)
# 13:30 to 14:00 -> [810, 840)
# 15:00 to 16:00 -> [900, 960)
ashley_busy = [(540, 570), (630, 750), (810, 840), (900, 960)]
add_busy_constraints(solver, ashley_busy)

# Jonathan's busy intervals:
# 9:00 to 10:00   -> [540, 600)
# 10:30 to 11:30  -> [630, 690)
# 12:30 to 15:00  -> [750, 900)
# 15:30 to 17:00  -> [930, 1020)
jonathan_busy = [(540, 600), (630, 690), (750, 900), (930, 1020)]
add_busy_constraints(solver, jonathan_busy)

# Walter's busy intervals:
# 9:00 to 9:30   -> [540, 570)
# 10:30 to 17:00 -> [630, 1020)
walter_busy = [(540, 570), (630, 1020)]
add_busy_constraints(solver, walter_busy)

# Since we want to find a time that works for everyone,
# let's iterate over possible start times in increasing order (earliest available).
found = False
for t in range(540, 1020 - duration + 1):
    solver.push()
    solver.add(start == t)
    if solver.check() == sat:
        meeting_start = t
        meeting_end = t + duration
        start_hr, start_min = divmod(meeting_start, 60)
        end_hr, end_min = divmod(meeting_end, 60)
        print("A valid meeting time is from {:02d}:{:02d} to {:02d}:{:02d}."
              .format(start_hr, start_min, end_hr, end_min))
        found = True
        solver.pop()
        break
    solver.pop()

if not found:
    print("No valid meeting time could be found.")