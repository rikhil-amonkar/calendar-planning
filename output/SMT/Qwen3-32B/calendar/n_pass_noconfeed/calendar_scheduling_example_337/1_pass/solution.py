from z3 import *

def to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

solver = Solver()

start = Int('start')

# Work hours constraints (9:00 to 17:00, 540 to 1020 minutes)
solver.add(start >= 540)
solver.add(start + 30 <= 1020)

# Participants' busy intervals in minutes
participants = {
    'John': [(690, 720), (840, 870)],
    'Megan': [(720, 750), (840, 900), (930, 960)],
    'Brandon': [],
    'Kimberly': [(540, 570), (600, 630), (660, 870), (900, 960), (990, 1020)],
    'Sean': [(600, 660), (690, 840), (900, 930)],
    'Lori': [(540, 570), (630, 720), (780, 870), (960, 990)],
}

# Add constraints for each participant's busy intervals
for intervals in participants.values():
    for (s, e) in intervals:
        solver.add(Or(start + 30 <= s, start >= e))

if solver.check() == sat:
    model = solver.model()
    start_val = model[start].as_long()
    end_val = start_val + 30
    start_time = to_time(start_val)
    end_time = to_time(end_val)
    print(f"Monday {start_time}:{end_time}")
else:
    print("No solution found")