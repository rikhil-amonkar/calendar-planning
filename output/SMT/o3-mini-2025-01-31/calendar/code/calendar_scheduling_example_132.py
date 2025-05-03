from z3 import *

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters.
# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
# Meeting duration: 30 minutes, so we require start >= 540 and start + 30 <= 1020.
duration = 30
start = Int('start')
solver.add(start >= 540, start + duration <= 1020)

# Helper function to add constraint that the meeting (start, start+duration)
# does not overlap with a busy interval [bs, be).
def add_busy_constraints(solver, busy_intervals):
    for bs, be in busy_intervals:
        solver.add(Or(start + duration <= bs, start >= be))
        
# Joe's calendar is wide open, so no busy intervals for Joe.

# Diana's busy intervals:
# 10:30 to 11:00 -> [630, 660]
# 12:30 to 13:00 -> [750, 780]
# 14:30 to 15:00 -> [870, 900]
# 15:30 to 16:00 -> [930, 960]
diana_busy = [(630, 660), (750, 780), (870, 900), (930, 960)]
add_busy_constraints(solver, diana_busy)

# Harold's busy intervals:
# 10:00 to 11:00 -> [600, 660]
# 11:30 to 16:30 -> [690, 990]
harold_busy = [(600, 660), (690, 990)]
add_busy_constraints(solver, harold_busy)

# Philip's busy intervals:
# 9:00 to 9:30   -> [540, 570]
# 10:30 to 12:00 -> [630, 720]
# 12:30 to 13:30 -> [750, 810]
# 14:00 to 17:00 -> [840, 1020]
philip_busy = [(540, 570), (630, 720), (750, 810), (840, 1020)]
add_busy_constraints(solver, philip_busy)

# Check for a valid meeting time that satisfies all constraints.
if solver.check() == sat:
    model = solver.model()
    meeting_start = model[start].as_long()
    meeting_end = meeting_start + duration
    start_hour, start_min = divmod(meeting_start, 60)
    end_hour, end_min = divmod(meeting_end, 60)
    print("A valid meeting time is from {:02d}:{:02d} to {:02d}:{:02d}".format(
        start_hour, start_min, end_hour, end_min))
else:
    print("No valid meeting time could be found.")