from z3 import *

solver = Solver()

day = Int('day')
start_time = Int('start_time')

# Constraints on day and start_time
solver.add(And(day >= 0, day <= 3))
solver.add(And(start_time >= 540, start_time <= 960))

# Busy periods for Natalie and William
natalie_busy = [
    # Monday (0)
    [(540, 570), (600, 720), (750, 780), (840, 870), (900, 990)],
    # Tuesday (1)
    [(540, 570), (600, 630), (750, 840), (960, 1020)],
    # Wednesday (2)
    [(660, 690), (960, 990)],
    # Thursday (3)
    [(600, 660), (690, 900), (930, 960), (990, 1020)],
]

william_busy = [
    # Monday (0)
    [(570, 660), (690, 1020)],
    # Tuesday (1)
    [(540, 780), (810, 960)],
    # Wednesday (2)
    [(540, 750), (780, 870), (930, 960), (990, 1020)],
    # Thursday (3)
    [(540, 630), (660, 690), (720, 750), (780, 840), (900, 1020)],
]

# Add constraints for each day and busy period
for d in range(4):
    all_busy = natalie_busy[d] + william_busy[d]
    for (s, e) in all_busy:
        solver.add(Implies(day == d, Or(start_time + 60 <= s, start_time >= e)))

if solver.check() == sat:
    model = solver.model()
    day_val = model[day].as_long()
    start_val = model[start_time].as_long()
    end_val = start_val + 60

    days = ["Monday", "Tuesday", "Wednesday", "Thursday"]
    day_name = days[day_val]

    def format_time(minutes):
        hours = minutes // 60
        mins = minutes % 60
        return f"{hours:02d}:{mins:02d}"

    start_str = format_time(start_val)
    end_str = format_time(end_val)

    print(f"{day_name} {start_str}:{end_str}")
else:
    print("No solution found")