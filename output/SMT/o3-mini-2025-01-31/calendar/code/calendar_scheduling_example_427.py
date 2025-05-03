from z3 import Solver, Int, Or, sat

# Create a Z3 solver instance
solver = Solver()

# Meeting parameters:
# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
# Meeting duration: 30 minutes.
duration = 30
start = Int("start")  # Meeting start time in minutes since midnight

# Constrain the meeting to be within work hours
solver.add(start >= 540, start + duration <= 1020)

# Helper function to add constraints so that the meeting does not overlap a busy interval.
def add_busy_constraints(solver, busy_intervals):
    for busy_start, busy_end in busy_intervals:
        # The meeting must finish before the busy interval starts or start after the busy interval ends.
        solver.add(Or(start + duration <= busy_start, start >= busy_end))

# Nancy's busy intervals:
# 11:30 to 12:00 -> [690, 720)
# 16:30 to 17:00 -> [990, 1020)
nancy_busy = [(690, 720), (990, 1020)]
add_busy_constraints(solver, nancy_busy)

# Gloria is free the entire day: no constraints

# Harold's busy intervals:
# 9:00 to 9:30    -> [540, 570)
# 10:30 to 11:00  -> [630, 660)
# 11:30 to 12:00  -> [690, 720)
# 12:30 to 13:00  -> [750, 780)
# 15:00 to 15:30  -> [900, 930)
# 16:30 to 17:00  -> [990, 1020)
harold_busy = [(540, 570), (630, 660), (690, 720), (750, 780), (900, 930), (990, 1020)]
add_busy_constraints(solver, harold_busy)

# Katherine has no meetings: no constraints

# Tyler's busy intervals:
# 9:00 to 9:30    -> [540, 570)
# 10:00 to 10:30  -> [600, 630)
# 11:00 to 12:30  -> [660, 750)
# 13:30 to 15:00  -> [810, 900)
# 15:30 to 16:30  -> [930, 990)
tyler_busy = [(540, 570), (600, 630), (660, 750), (810, 900), (930, 990)]
add_busy_constraints(solver, tyler_busy)

# Larry's busy intervals:
# 10:00 to 11:00   -> [600, 660)
# 11:30 to 13:00   -> [690, 780)
# 13:30 to 14:30   -> [810, 870)
# 15:00 to 16:00   -> [900, 960)
# 16:30 to 17:00   -> [990, 1020)
larry_busy = [(600, 660), (690, 780), (810, 870), (900, 960), (990, 1020)]
add_busy_constraints(solver, larry_busy)

# Mark's busy intervals:
# 9:00 to 9:30    -> [540, 570)
# 10:00 to 14:30   -> [600, 870)
# 15:00 to 17:00   -> [900, 1020)
mark_busy = [(540, 570), (600, 870), (900, 1020)]
add_busy_constraints(solver, mark_busy)

# Try all possible start times in the work hours to find a valid meeting slot.
found = False
for t in range(540, 1020 - duration + 1):
    solver.push()
    solver.add(start == t)
    if solver.check() == sat:
        meeting_start = t
        meeting_end = t + duration
        start_hr, start_min = divmod(meeting_start, 60)
        end_hr, end_min = divmod(meeting_end, 60)
        print("A valid meeting time is from {:02d}:{:02d} to {:02d}:{:02d}".format(
            start_hr, start_min, end_hr, end_min))
        found = True
        solver.pop()
        break
    solver.pop()

if not found:
    print("No valid meeting time could be found.")