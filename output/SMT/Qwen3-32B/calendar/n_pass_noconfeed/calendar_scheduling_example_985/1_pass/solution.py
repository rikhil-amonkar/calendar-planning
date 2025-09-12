from z3 import *

solver = Solver()

day = Int('day')
start_time = Int('start_time')

solver.add(And(day >= 0, day <= 4))
solver.add(And(start_time >= 540, start_time <= 960))

diane_busy = {
    0: [(720, 750), (900, 930)],
    1: [(600, 660), (690, 720), (750, 780), (960, 1020)],
    2: [(540, 570), (870, 900), (990, 1020)],
    3: [(930, 990)],
    4: [(570, 690), (870, 900), (960, 1020)]
}

matthew_busy = {
    0: [(540, 600), (630, 1020)],
    1: [(540, 1020)],
    2: [(540, 660), (720, 870), (960, 1020)],
    3: [(540, 960)],
    4: [(540, 1020)]
}

for d in range(5):
    diane_intervals = diane_busy[d]
    matthew_intervals = matthew_busy[d]
    
    diane_constraints = []
    for b_start, b_end in diane_intervals:
        diane_constraints.append(Or(start_time + 60 <= b_start, start_time >= b_end))
    
    matthew_constraints = []
    for b_start, b_end in matthew_intervals:
        matthew_constraints.append(Or(start_time + 60 <= b_start, start_time >= b_end))
    
    day_constraints = And(And(diane_constraints), And(matthew_constraints))
    solver.add(Implies(day == d, day_constraints))

solver.add(Implies(day == 2, start_time >= 750))

if solver.check() == sat:
    model = solver.model()
    day_val = model[day].as_long()
    start_val = model[start_time].as_long()
    
    days = ["Monday", "Tuesday", "Wednesday", "Thursday", "Friday"]
    day_name = days[day_val]
    
    start_h = start_val // 60
    start_m = start_val % 60
    end_val = start_val + 60
    end_h = end_val // 60
    end_m = end_val % 60
    
    time_str = f"{start_h:02d}:{start_m:02d}:{end_h:02d}:{end_m:02d}"
    print(f"{day_name} {time_str}")
else:
    print("No solution found")