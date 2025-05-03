from z3 import Solver, Int, Or, sat

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters:
# Working hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
# Meeting duration: 30 minutes.
duration = 30
start = Int("start")  # Meeting start time, in minutes since midnight

# The meeting must be scheduled within work hours.
solver.add(start >= 540, start + duration <= 1020)

# Helper function that adds constraints so that the meeting does not overlap a given busy interval.
def add_busy_constraints(solver, busy_intervals):
    for busy_start, busy_end in busy_intervals:
        # The meeting must finish before busy_start, or start after busy_end.
        solver.add(Or(start + duration <= busy_start, start >= busy_end))

# Anthony: free all day => no constraints.

# Teresa: free all day => no constraints.

# Vincent's busy intervals:
# 10:00 to 10:30 -> [600, 630)
# 11:30 to 12:30 -> [690, 750)
# 13:30 to 14:00 -> [810, 840)
# 16:00 to 17:00 -> [960, 1020)
vincent_busy = [(600, 630), (690, 750), (810, 840), (960, 1020)]
add_busy_constraints(solver, vincent_busy)

# Kevin's busy intervals:
# 9:00 to 9:30   -> [540, 570)
# 10:30 to 11:00 -> [630, 660)
# 11:30 to 12:00 -> [690, 720)
# 12:30 to 13:30 -> [750, 810)
# 16:00 to 16:30 -> [960, 990)
kevin_busy = [(540, 570), (630, 660), (690, 720), (750, 810), (960, 990)]
add_busy_constraints(solver, kevin_busy)

# Julie's busy intervals:
# 9:00 to 9:30   -> [540, 570)
# 10:00 to 11:30 -> [600, 690)
# 12:00 to 12:30 -> [720, 750)
# 13:00 to 14:00 -> [780, 840)
# 15:00 to 16:30 -> [900, 990)
julie_busy = [(540, 570), (600, 690), (720, 750), (780, 840), (900, 990)]
add_busy_constraints(solver, julie_busy)

# Tyler's busy intervals:
# 9:30 to 10:00  -> [570, 600)
# 10:30 to 12:00 -> [630, 720)
# 12:30 to 13:00 -> [750, 780)
# 13:30 to 14:00 -> [810, 840)
# 14:30 to 15:00 -> [870, 900)
# 16:00 to 16:30 -> [960, 990)
tyler_busy = [(570, 600), (630, 720), (750, 780), (810, 840), (870, 900), (960, 990)]
add_busy_constraints(solver, tyler_busy)

# Bryan's busy intervals:
# 9:00 to 12:30  -> [540, 750)
# 13:00 to 14:00 -> [780, 840)
# 14:30 to 17:00 -> [870, 1020)
bryan_busy = [(540, 750), (780, 840), (870, 1020)]
add_busy_constraints(solver, bryan_busy)

# Now search for a valid meeting time.
found = False
# The meeting start time must be such that start + duration <= 1020.
# Hence, potential start times are in [540, 990].
for t in range(540, 1020 - duration + 1):
    solver.push()
    solver.add(start == t)
    if solver.check() == sat:
        meeting_start = t
        meeting_end = t + duration
        start_hour, start_minute = divmod(meeting_start, 60)
        end_hour, end_minute = divmod(meeting_end, 60)
        print("A valid meeting time is from {:02d}:{:02d} to {:02d}:{:02d}".format(start_hour, start_minute, end_hour, end_minute))
        found = True
        solver.pop()
        break
    solver.pop()

if not found:
    print("No valid meeting time could be found.")