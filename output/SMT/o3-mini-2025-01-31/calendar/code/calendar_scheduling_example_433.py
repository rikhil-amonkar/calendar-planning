from z3 import Solver, Int, Or, sat

# Create a Z3 solver.
solver = Solver()

# Meeting parameters:
# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
# Meeting duration: 30 minutes.
duration = 30
start = Int("start")  # The start time in minutes since midnight.

# Constrain meeting time to be within work hours.
solver.add(start >= 540, start + duration <= 1020)

# Helper function: for each busy interval, the meeting must either finish before
# the interval starts or begin after the interval ends.
def add_busy_constraints(solver, busy_intervals):
    for busy_start, busy_end in busy_intervals:
        solver.add(Or(start + duration <= busy_start, start >= busy_end))

# Diane is free the entire day, so no busy intervals from her.

# Terry's busy intervals:
# 9:30 to 10:00   -> [570,600)
# 11:00 to 11:30  -> [660,690)
# 12:00 to 12:30  -> [720,750)
# 13:00 to 13:30  -> [780,810)
# 15:30 to 16:00  -> [930,960)
# 16:30 to 17:00  -> [990,1020)
terry_busy = [(570,600), (660,690), (720,750), (780,810), (930,960), (990,1020)]
add_busy_constraints(solver, terry_busy)

# Jessica's busy intervals:
# 9:30 to 11:00   -> [570,660)
# 15:00 to 16:30  -> [900,990)
jessica_busy = [(570,660), (900,990)]
add_busy_constraints(solver, jessica_busy)

# Peter is free the whole day.

# Gary's busy intervals:
# 9:00 to 11:30   -> [540,690)
# 12:00 to 16:00  -> [720,960)
# 16:30 to 17:00  -> [990,1020)
gary_busy = [(540,690), (720,960), (990,1020)]
add_busy_constraints(solver, gary_busy)

# Gabriel's busy intervals:
# 10:00 to 11:30  -> [600,690)
# 12:00 to 12:30  -> [720,750)
# 13:00 to 14:00  -> [780,840)
# 14:30 to 15:30  -> [870,930)
gabriel_busy = [(600,690), (720,750), (780,840), (870,930)]
add_busy_constraints(solver, gabriel_busy)

# Amanda's busy intervals:
# 9:00 to 9:30    -> [540,570)
# 10:00 to 11:30  -> [600,690)
# 12:00 to 13:00  -> [720,780)
# 13:30 to 14:00  -> [810,840)
# 14:30 to 17:00  -> [870,1020)
amanda_busy = [(540,570), (600,690), (720,780), (810,840), (870,1020)]
add_busy_constraints(solver, amanda_busy)

# Search for a valid meeting start time by iterating over each minute in the allowable range.
found = False
for t in range(540, 1020 - duration + 1):
    solver.push()
    solver.add(start == t)
    if solver.check() == sat:
        meeting_start = t
        meeting_end = t + duration
        start_hr, start_min = divmod(meeting_start, 60)
        end_hr, end_min = divmod(meeting_end, 60)
        print("A valid meeting time is from {:02d}:{:02d} to {:02d}:{:02d}".format(start_hr, start_min, end_hr, end_min))
        found = True
        solver.pop()
        break
    solver.pop()

if not found:
    print("No valid meeting time could be found.")