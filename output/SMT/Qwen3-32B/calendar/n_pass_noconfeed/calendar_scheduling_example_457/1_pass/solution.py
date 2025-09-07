from z3 import *

# Define busy intervals in minutes since midnight
participants = {
    'Andrea': [(570, 630), (810, 870)],
    'Ruth': [(750, 780), (900, 930)],
    'Steven': [(600, 630), (660, 690), (720, 750), (810, 840), (900, 960)],
    'Grace': [],
    'Kyle': [(540, 570), (630, 720), (750, 780), (810, 900), (930, 960), (990, 1020)],
    'Elijah': [(540, 660), (690, 750), (810, 840), (930, 960), (990, 1020)],
    'Lori': [(540, 570), (600, 690), (720, 810), (840, 960), (990, 1020)],
}

solver = Solver()
start = Int('start')

# Meeting must start between 9:00 (540) and 17:00 - 30 min = 16:30 (990)
solver.add(start >= 540)
solver.add(start <= 990)

# For each participant's busy intervals, add constraints
for person in participants:
    for (bs, be) in participants[person]:
        solver.add(Or(start + 30 <= bs, start >= be))

if solver.check() == sat:
    model = solver.model()
    start_val = model[start].as_long()
    # Convert start_val to HH:MM format
    start_hour = start_val // 60
    start_minute = start_val % 60
    end_val = start_val + 30
    end_hour = end_val // 60
    end_minute = end_val % 60
    # Format with leading zeros if needed
    def format_time(h, m):
        return f"{h:02d}:{m:02d}"
    start_time = format_time(start_hour, start_minute)
    end_time = format_time(end_hour, end_minute)
    print(f"{start_time}:{end_time} Monday")
else:
    print("No solution found")