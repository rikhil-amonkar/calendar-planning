from z3 import Solver, Int, Or, Implies, sat

solver = Solver()
Day = Int('Day')
Start = Int('Start')

# Possible days: Monday (0), Tuesday (1), Friday (4). Betty can't meet on Wednesday/Thursday.
solver.add(Or(Day == 0, Day == 1, Day == 4))
solver.add(Start >= 0)
solver.add(Start + 60 <= 480)  # 1-hour meeting within 9:00-17:00

# Betty's time blocks converted to minutes since 9:00 for each day
betty_constraints = [
    (0, [(60, 90), (150, 210), (420, 450)]),    # Monday
    (1, [(30, 60), (90, 120), (180, 210), (270, 360), (420, 450)]),  # Tuesday
    (4, [(0, 60), (150, 180), (210, 240), (330, 360)])  # Friday
]

# Megan's time blocks converted to minutes since 9:00 for each day
megan_constraints = [
    (0, [(0, 480)]),                            # Monday (entire day blocked)
    (1, [(0, 30), (60, 90), (180, 300), (360, 390), (420, 450)]),  # Tuesday
    (4, [(0, 480)])                             # Friday (entire day blocked)
]

# Add constraints based on selected day
for d, blocks in betty_constraints:
    for (block_start, block_end) in blocks:
        solver.add(Implies(Day == d, Or(Start + 60 <= block_start, Start >= block_end)))

for d, blocks in megan_constraints:
    for (block_start, block_end) in blocks:
        solver.add(Implies(Day == d, Or(Start + 60 <= block_start, Start >= block_end)))

if solver.check() == sat:
    model = solver.model()
    day_num = model[Day].as_long()
    start_min = model[Start].as_long()
    days = ["Monday", "Tuesday", "Wednesday", "Thursday", "Friday"]
    
    start_h = 9 + start_min // 60
    start_m = start_min % 60
    end_min = start_min + 60
    end_h = 9 + end_min // 60
    end_m = end_min % 60
    
    print(f"{days[day_num]} {start_h:02d}:{start_m:02d}-{end_h:02d}:{end_m:02d}")
else:
    print("No solution found")