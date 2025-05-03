from z3 import *

# Create a Z3 solver instance.
solver = Solver()

# Set meeting parameters:
# Work hours: Monday 9:00 (540 minutes) to 17:00 (1020 minutes)
# Meeting duration: 30 minutes.
duration = 30
start = Int("start")

# Meeting must be scheduled within work hours.
solver.add(start >= 540, start + duration <= 1020)

# Helper function to add non-overlap constraints
def add_busy_constraints(solver, busy_intervals):
    # For each busy interval [bs, be), meeting must finish by bs, or start at or after be.
    for bs, be in busy_intervals:
        solver.add(Or(start + duration <= bs, start >= be))

# Douglas' blocked calendar:
#  10:00 to 10:30 -> [600, 630)
#  11:00 to 12:00 -> [660, 720)
#  12:30 to 13:00 -> [750, 780)
#  15:30 to 16:30 -> [930, 990)
douglas_busy = [(600, 630), (660, 720), (750, 780), (930, 990)]
add_busy_constraints(solver, douglas_busy)

# Gloria's blocked calendar:
#  10:30 to 11:00 -> [630, 660)
#  16:30 to 17:00 -> [990, 1020)
gloria_busy = [(630, 660), (990, 1020)]
add_busy_constraints(solver, gloria_busy)

# Peter's busy schedule:
#  9:00 to 10:00  -> [540, 600)
# 11:00 to 11:30  -> [660, 690)
# 12:30 to 13:30  -> [750, 810)
# 14:30 to 15:00  -> [870, 900)
# 16:00 to 17:00  -> [960, 1020)
peter_busy = [(540, 600), (660, 690), (750, 810), (870, 900), (960, 1020)]
add_busy_constraints(solver, peter_busy)

# Ryan's blocked calendar:
#  9:30 to 10:00 -> [570, 600)
# 10:30 to 11:30 -> [630, 690)
# 12:00 to 12:30 -> [720, 750)
# 13:00 to 14:00 -> [780, 840)
# 15:00 to 17:00 -> [900, 1020)
ryan_busy = [(570, 600), (630, 690), (720, 750), (780, 840), (900, 1020)]
add_busy_constraints(solver, ryan_busy)

# Search for the earliest meeting time that satisfies all constraints.
solution_found = False
# Meeting start times can be considered from 540 to 990 (1020 - 30).
for t in range(540, 991):
    solver.push()
    solver.add(start == t)
    if solver.check() == sat:
        model = solver.model()
        meeting_start = model[start].as_long()
        meeting_end = meeting_start + duration
        # Convert minutes to HH:MM for readability.
        start_hr, start_min = divmod(meeting_start, 60)
        end_hr, end_min = divmod(meeting_end, 60)
        print("A valid meeting time is from {:02d}:{:02d} to {:02d}:{:02d}".format(
            start_hr, start_min, end_hr, end_min))
        solution_found = True
        solver.pop()
        break
    solver.pop()

if not solution_found:
    print("No valid meeting time could be found.")