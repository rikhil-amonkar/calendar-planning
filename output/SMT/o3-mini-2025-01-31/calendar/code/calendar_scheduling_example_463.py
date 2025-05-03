from z3 import Solver, Int, Or, sat

# Create a new solver instance.
solver = Solver()

# Meeting parameters:
# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
# Meeting duration is 30 minutes.
duration = 30
start = Int("start")  # meeting start time in minutes since midnight

# Ensure the meeting is within work hours.
solver.add(start >= 540, start + duration <= 1020)

# Helper function to add non-overlap constraints for busy intervals.
def add_busy_constraints(solver, busy_intervals):
    for busy_start, busy_end in busy_intervals:
        # The meeting [start, start+duration) must end before the busy interval begins, 
        # or start after the busy interval ends.
        solver.add(Or(start + duration <= busy_start, start >= busy_end))

# Define busy intervals for each participant (in minutes).

# Joyce's busy intervals:
# 10:30 to 11:30 -> [630, 690)
# 12:30 to 14:00 -> [750, 840)
# 15:00 to 15:30 -> [900, 930)
joyce_busy = [(630, 690), (750, 840), (900, 930)]
add_busy_constraints(solver, joyce_busy)

# Diana's busy intervals:
# 9:00 to 9:30  -> [540, 570)
# 16:00 to 16:30 -> [960, 990)
diana_busy = [(540, 570), (960, 990)]
add_busy_constraints(solver, diana_busy)

# Emma's busy intervals:
# 9:00 to 9:30  -> [540, 570)
# 12:00 to 12:30 -> [720, 750)
# 13:00 to 13:30 -> [780, 810)
# 14:00 to 14:30 -> [840, 870)
emma_busy = [(540, 570), (720, 750), (780, 810), (840, 870)]
add_busy_constraints(solver, emma_busy)

# Gregory's busy intervals:
# 10:00 to 10:30 -> [600, 630)
# 16:30 to 17:00 -> [990, 1020)
gregory_busy = [(600, 630), (990, 1020)]
add_busy_constraints(solver, gregory_busy)

# Tyler's busy intervals:
# 9:00 to 9:30   -> [540, 570)
# 10:00 to 10:30  -> [600, 630)
# 11:00 to 14:00  -> [660, 840)
tyler_busy = [(540, 570), (600, 630), (660, 840)]
add_busy_constraints(solver, tyler_busy)

# Jacob's busy intervals:
# 9:00 to 11:00   -> [540, 660)
# 11:30 to 12:00  -> [690, 720)
# 12:30 to 14:00  -> [750, 840)
# 15:30 to 16:30  -> [930, 990)
jacob_busy = [(540, 660), (690, 720), (750, 840), (930, 990)]
add_busy_constraints(solver, jacob_busy)

# Bruce's busy intervals:
# 9:00 to 9:30   -> [540, 570)
# 10:00 to 11:30  -> [600, 690)
# 12:00 to 14:30  -> [720, 870)
# 15:00 to 16:00  -> [900, 960)
# 16:30 to 17:00  -> [990, 1020)
bruce_busy = [(540, 570), (600, 690), (720, 870), (900, 960), (990, 1020)]
add_busy_constraints(solver, bruce_busy)

# Since we need to find a valid time that works for everyone,
# we'll iterate over possible start times in increasing order to discover the earliest available time.
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