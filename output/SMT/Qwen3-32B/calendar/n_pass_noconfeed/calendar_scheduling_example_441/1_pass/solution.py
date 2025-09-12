from z3 import *

def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

solver = Solver()

s = Int('s')
e = s + 30

# Meeting must be between 9:00 (540) and 17:00 (1020)
solver.add(s >= 540)
solver.add(e <= 1020)

participants = {
    'Joan': [(690, 720), (870, 900)],
    'Megan': [(540, 600), (840, 870), (960, 990)],
    'Austin': [],
    'Betty': [(570, 600), (690, 720), (810, 840), (960, 990)],
    'Judith': [(540, 660), (720, 780), (840, 900)],
    'Terry': [(570, 600), (690, 750), (780, 840), (900, 930), (960, 1020)],
    'Kathryn': [(570, 600), (630, 660), (690, 780), (840, 960), (990, 1020)]
}

for busy_intervals in participants.values():
    for (start_b, end_b) in busy_intervals:
        solver.add(Or(s + 30 <= start_b, s >= end_b))

if solver.check() == sat:
    model = solver.model()
    s_val = model[s].as_long()
    e_val = s_val + 30
    start_time = minutes_to_time(s_val)
    end_time = minutes_to_time(e_val)
    print(f"{{{start_time}:{end_time}}} Monday")
else:
    print("No solution found.")