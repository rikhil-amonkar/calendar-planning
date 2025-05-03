from z3 import Solver, Int, Or, sat

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters:
# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
# Meeting duration: 30 minutes.
duration = 30
start = Int("start")  # Meeting start time in minutes since midnight

# Ensure the meeting is scheduled within work hours.
solver.add(start >= 540, start + duration <= 1020)

# Helper function to add non-overlap constraints for a list of busy intervals.
def add_busy_constraints(solver, busy_intervals):
    for busy_start, busy_end in busy_intervals:
        # The meeting [start, start+duration) must either finish before the busy interval starts
        # or start after the busy interval ends.
        solver.add(Or(start + duration <= busy_start, start >= busy_end))

# William is free the entire day. No constraints.

# Julia's busy intervals:
# 10:00 to 10:30 --> [600, 630)
# 12:00 to 12:30 --> [720, 750)
# 13:00 to 14:00 --> [780, 840)
# 15:30 to 16:30 --> [930, 990)
julia_busy = [(600, 630), (720, 750), (780, 840), (930, 990)]
add_busy_constraints(solver, julia_busy)

# Katherine is free the entire day. No constraints.

# Diana is free the entire day. No constraints.

# Philip's busy intervals:
# 10:00 to 11:00 --> [600, 660)
# 12:30 to 13:30 --> [750, 810)
# 15:00 to 17:00 --> [900, 1020)
philip_busy = [(600, 660), (750, 810), (900, 1020)]
add_busy_constraints(solver, philip_busy)

# Ashley's busy intervals:
# 9:00 to 11:30   --> [540, 690)
# 12:00 to 14:00  --> [720, 840)
# 14:30 to 15:30  --> [870, 930)
# 16:00 to 16:30  --> [960, 990)
ashley_busy = [(540, 690), (720, 840), (870, 930), (960, 990)]
add_busy_constraints(solver, ashley_busy)

# Mark's busy intervals:
# 9:30 to 11:30   --> [570, 690)
# 12:30 to 14:30  --> [750, 870)
# 15:00 to 16:00  --> [900, 960)
mark_busy = [(570, 690), (750, 870), (900, 960)]
add_busy_constraints(solver, mark_busy)

# Now iterate over the possible start times (in minutes) to find a valid meeting time.
found = False
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