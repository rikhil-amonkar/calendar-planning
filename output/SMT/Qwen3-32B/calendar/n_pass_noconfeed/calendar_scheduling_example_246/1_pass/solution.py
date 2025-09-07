from z3 import *

def to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

solver = Solver()

start = Int('start')

# Work hours are 9:00 (540) to 17:00 (1020). Meeting is 30 minutes, so start must be <= 990
solver.add(And(start >= 540, start <= 990))

# Define busy times for each participant
participants = {
    'Jacob': [(810, 840), (870, 900)],
    'Diana': [(570, 600), (690, 720), (780, 810), (960, 990)],
    'Adam': [(570, 630), (660, 750), (930, 960)],
    'Angela': [(570, 600), (630, 720), (780, 930), (960, 990)],
    'Dennis': [(540, 570), (630, 690), (780, 900), (990, 1020)]
}

for busy_times in participants.values():
    for b_start, b_end in busy_times:
        solver.add(Or(start + 30 <= b_start, start >= b_end))

if solver.check() == sat:
    model = solver.model()
    start_val = model[start].as_long()
    start_time = to_time(start_val)
    end_time = to_time(start_val + 30)
    print(f"{{{start_time}:{end_time}}} Monday")
else:
    print("No solution found.")