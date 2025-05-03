from z3 import *

# Create a Z3 solver instance.
solver = Solver()

# Define work hours in minutes: Monday 9:00 (540) to 17:00 (1020)
# Meeting duration of 30 minutes.
duration = 30
start = Int("start")  # Meeting start time in minutes since midnight

# Basic constraint: meeting must occur within work hours.
solver.add(start >= 540, start + duration <= 1020)

# William's preference: he would rather not meet on Monday after 13:30.
# We interpret this as the meeting should finish by 13:30 (13*60+30 = 810).
solver.add(start + duration <= 810)

# Helper function to add constraints so that the meeting does not overlap with a busy interval.
def add_busy_constraints(solver, busy_intervals):
    for bs, be in busy_intervals:
        # For each busy interval [bs, be), the meeting must finish before bs or start at/after be.
        solver.add(Or(start + duration <= bs, start >= be))

# Evelyn's busy intervals:
#   9:30 to 10:00 -> [570,600)
#   11:30 to 12:00 -> [690,720)
evelyn_busy = [(570, 600), (690, 720)]
add_busy_constraints(solver, evelyn_busy)

# Roy is free the entire day (no constraints).

# Billy is free the entire day (no constraints).

# Gregory's busy intervals:
#   10:00 to 10:30 -> [600,630)
#   16:00 to 16:30 -> [960,990)
# (Note: the later meeting does not matter as our meeting is forced to finish by 810.)
gregory_busy = [(600, 630), (960, 990)]
add_busy_constraints(solver, gregory_busy)

# Vincent's busy intervals:
#   10:00 to 10:30 -> [600,630)
#   11:00 to 12:00 -> [660,720)
#   12:30 to 13:00 -> [750,780)
#   13:30 to 14:00 -> [810,840)  <-- Outside our window due to William's preference.
#   15:00 to 16:30 -> [900,990)  <-- Also outside our window.
vincent_busy = [(600, 630), (660, 720), (750, 780), (810, 840), (900, 990)]
add_busy_constraints(solver, vincent_busy)

# Philip's busy intervals:
#   9:00 to 10:30  -> [540,630)
#   11:00 to 11:30 -> [660,690)
#   12:00 to 13:00 -> [720,780)
#   15:00 to 17:00 -> [900,1020)  <-- Outside our window.
philip_busy = [(540, 630), (660, 690), (720, 780), (900, 1020)]
add_busy_constraints(solver, philip_busy)

# William's busy intervals:
#   9:00 to 10:00   -> [540,600)
#   11:00 to 13:00  -> [660,780)
#   13:30 to 14:30  -> [810,870)
#   15:00 to 17:00  -> [900,1020)
william_busy = [(540, 600), (660, 780), (810, 870), (900, 1020)]
add_busy_constraints(solver, william_busy)

# We'll iterate over possible meeting start times minute-by-minute within the effective window.
# Because of William's constraint, start+duration <= 810, so start <= 780.
found = False
for t in range(540, 781):  # t from 9:00 (540) to 13:00 (780) inclusive
    solver.push()          # Save the current state.
    solver.add(start == t)
    if solver.check() == sat:
        meeting_start = t
        meeting_end = t + duration
        start_hour, start_min = divmod(meeting_start, 60)
        end_hour, end_min = divmod(meeting_end, 60)
        print("A valid meeting time is from {:02d}:{:02d} to {:02d}:{:02d}".\
              format(start_hour, start_min, end_hour, end_min))
        found = True
        solver.pop()       # Restore the state.
        break
    solver.pop()

if not found:
    print("No valid meeting time could be found.")