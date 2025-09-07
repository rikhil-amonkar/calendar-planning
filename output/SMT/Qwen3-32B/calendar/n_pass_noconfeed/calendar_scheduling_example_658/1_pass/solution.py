from z3 import *

solver = Solver()

day = Int('day')
start = Int('start')

solver.add(Or(day == 0, day == 1))

# Monday constraints
monday_time = And(start >= 540, start <= 990)
shirley_mon_1 = Or(start + 30 <= 630, 660 <= start)
shirley_mon_2 = Or(start + 30 <= 720, 750 <= start)
shirley_mon_3 = Or(start + 30 <= 960, 990 <= start)
albert_mon = Or(start + 30 <= 540, 1020 <= start)
monday_constraints = And(monday_time, shirley_mon_1, shirley_mon_2, shirley_mon_3, albert_mon)

# Tuesday constraints
tuesday_time = And(start >= 540, start <= 990)
shirley_pref = start + 30 <= 630
shirley_tue = Or(start + 30 <= 570, 600 <= start)
albert_tue_1 = Or(start + 30 <= 570, 600 <= start)
albert_tue_2 = Or(start + 30 <= 690, 750 <= start)
albert_tue_3 = Or(start + 30 <= 780, 960 <= start)
albert_tue_4 = Or(start + 30 <= 990, 1020 <= start)
tuesday_constraints = And(tuesday_time, shirley_pref, shirley_tue, albert_tue_1, albert_tue_2, albert_tue_3, albert_tue_4)

solver.add(Implies(day == 0, monday_constraints))
solver.add(Implies(day == 1, tuesday_constraints))

if solver.check() == sat:
    model = solver.model()
    day_val = model[day].as_long()
    start_val = model[start].as_long()
    day_name = "Monday" if day_val == 0 else "Tuesday"
    start_h = (start_val) // 60
    start_m = (start_val) % 60
    end_val = start_val + 30
    end_h = end_val // 60
    end_m = end_val % 60
    start_time = f"{start_h:02d}:{start_m:02d}"
    end_time = f"{end_h:02d}:{end_m:02d}"
    print(f"{day_name} {start_time}:{end_time}")
else:
    print("No solution found")