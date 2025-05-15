from z3 import Solver, Int, Or, Implies, sat

solver = Solver()
Day = Int('Day')
Start = Int('Start')

# Meeting must be on Tuesday (Margaret can't meet on Monday, and Tuesday only after 14:30)
solver.add(Day == 1)  # Tuesday is day 1 (0=Monday, 1=Tuesday)
solver.add(Start >= 330)  # 14:30 = 330 minutes after 9:00
solver.add(Start + 30 <= 480)  # 17:00

# Margaret's Tuesday blocked time (12:00-12:30=180-210) - irrelevant due to start >=330
# Explicitly add in case of model variations
solver.add(Implies(Day == 1, Or(Start + 30 <= 180, Start >= 210)))

# Alexis's Tuesday blocked times (9:00-9:30=0-30, 10:00-10:30=60-90, 14:00-16:30=300-450)
alexis_blocks = [(0, 30), (60, 90), (300, 450)]
for (block_start, block_end) in alexis_blocks:
    solver.add(Implies(Day == 1, Or(Start + 30 <= block_start, Start >= block_end)))

if solver.check() == sat:
    model = solver.model()
    start_min = model[Start].as_long()
    day_str = "Tuesday"
    
    start_h = 9 + start_min // 60
    start_m = start_min % 60
    end_min = start_min + 30
    end_h = 9 + end_min // 60
    end_m = end_min % 60
    
    print(f"{day_str} {start_h:02d}:{start_m:02d}-{end_h:02d}:{end_m:02d}")
else:
    print("No solution found")