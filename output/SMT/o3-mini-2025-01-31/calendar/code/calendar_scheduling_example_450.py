from z3 import Solver, Int, Or, sat

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters:
# Working hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
# Meeting duration: 30 minutes.
duration = 30
start = Int("start")  # Meeting start time in minutes since midnight

# Constrain the meeting to occur within work hours.
solver.add(start >= 540, start + duration <= 1020)

# Helper function to add busy interval constraints.
# For each busy interval [busy_start, busy_end), the meeting interval [start, start + duration)
# must either finish before busy_start or start at/after busy_end.
def add_busy_constraints(solver, busy_intervals):
    for busy_start, busy_end in busy_intervals:
        solver.add(Or(start + duration <= busy_start, start >= busy_end))

# Jonathan's busy intervals:
# 9:30 to 10:00 -> [570, 600)
# 12:30 to 13:30 -> [750, 810)
# 14:30 to 15:00 -> [870, 900)
jonathan_busy = [(570, 600), (750, 810), (870, 900)]
add_busy_constraints(solver, jonathan_busy)

# Janice's busy intervals:
# 9:00 to 9:30  -> [540, 570)
# 11:30 to 12:00 -> [690, 720)
# 12:30 to 13:30 -> [750, 810)
# 14:30 to 15:00 -> [870, 900)
# 16:00 to 16:30 -> [960, 990)
janice_busy = [(540, 570), (690, 720), (750, 810), (870, 900), (960, 990)]
add_busy_constraints(solver, janice_busy)

# Walter's busy intervals:
# 9:30 to 10:00 -> [570, 600)
# 11:30 to 12:00 -> [690, 720)
walter_busy = [(570, 600), (690, 720)]
add_busy_constraints(solver, walter_busy)

# Mary's busy intervals:
# 12:00 to 12:30 -> [720, 750)
# 13:30 to 14:00 -> [810, 840)
mary_busy = [(720, 750), (810, 840)]
add_busy_constraints(solver, mary_busy)

# Roger's busy intervals:
# 9:30 to 10:30  -> [570, 630)
# 11:00 to 12:30 -> [660, 750)
# 13:00 to 13:30 -> [780, 810)
# 14:00 to 15:30 -> [840, 930)
# 16:00 to 16:30 -> [960, 990)
roger_busy = [(570, 630), (660, 750), (780, 810), (840, 930), (960, 990)]
add_busy_constraints(solver, roger_busy)

# Tyler's busy intervals:
# 9:30 to 11:00   -> [570, 660)
# 11:30 to 12:30  -> [690, 750)
# 13:30 to 14:00  -> [810, 840)
# 15:00 to 16:00  -> [900, 960)
tyler_busy = [(570, 660), (690, 750), (810, 840), (900, 960)]
add_busy_constraints(solver, tyler_busy)

# Arthur's busy intervals:
# 10:00 to 11:30  -> [600, 690)
# 12:30 to 13:00  -> [750, 780)
# 13:30 to 14:00  -> [810, 840)
# 14:30 to 16:00  -> [870, 960)
arthur_busy = [(600, 690), (750, 780), (810, 840), (870, 960)]
add_busy_constraints(solver, arthur_busy)

# Iterate over possible meeting start times (each minute within work hours)
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