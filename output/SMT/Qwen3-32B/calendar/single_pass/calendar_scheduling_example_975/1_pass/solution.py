from z3 import *

# Define busy intervals for Nicole and Daniel
nicole_busy = {
    0: [],  # Monday
    1: [(16*60, 16*60 + 30)],  # Tuesday 16:00-16:30
    2: [(15*60, 15*60 + 30)],  # Wednesday 15:00-15:30
    3: [],  # Thursday
    4: [(12*60, 12*60 + 30), (15*60 + 30, 16*60)]  # Friday
}

daniel_busy = {
    0: [(540, 750), (780, 810), (840, 990)],  # Monday
    1: [(540, 630), (690, 750), (780, 810), (900, 960), (990, 1020)],  # Tuesday
    2: [(540, 600), (660, 750), (780, 810), (840, 870), (990, 1020)],  # Wednesday
    3: [(660, 720), (780, 840), (900, 930)],  # Thursday
    4: [(600, 660), (690, 720), (750, 870), (900, 930), (960, 990)]  # Friday
}

opt = Optimize()

day = Int('day')
start = Int('start')

opt.add(And(day >= 0, day <= 4))
opt.add(And(start >= 540, start <= 960))  # 9:00 to 16:00

# Add constraints for Nicole
nicole_constraints = []
for d in range(5):
    per_day_constraints = []
    for (bs, be) in nicole_busy[d]:
        per_day_constraints.append(Or(start >= be, bs >= start + 60))
    if per_day_constraints:
        per_day_and = And(per_day_constraints)
    else:
        per_day_and = True
    implication = Implies(day == d, per_day_and)
    nicole_constraints.append(implication)
opt.add(And(nicole_constraints))

# Add constraints for Daniel
daniel_constraints = []
for d in range(5):
    per_day_constraints = []
    for (bs, be) in daniel_busy[d]:
        per_day_constraints.append(Or(start >= be, bs >= start + 60))
    if per_day_constraints:
        per_day_and = And(per_day_constraints)
    else:
        per_day_and = True
    implication = Implies(day == d, per_day_and)
    daniel_constraints.append(implication)
opt.add(And(daniel_constraints))

# Set objectives to minimize day and then start time
opt.minimize(day)
opt.minimize(start)

if opt.check() == sat:
    model = opt.model()
    day_val = model.eval(day).as_long()
    start_val = model.eval(start).as_long()
    end_val = start_val + 60
    days = ["Monday", "Tuesday", "Wednesday", "Thursday", "Friday"]
    day_name = days[day_val]
    start_h = start_val // 60
    start_m = start_val % 60
    start_str = f"{start_h:02d}:{start_m:02d}"
    end_h = end_val // 60
    end_m = end_val % 60
    end_str = f"{end_h:02d}:{end_m:02d}"
    print("SOLUTION:")
    print(f"Day: {day_name}")
    print(f"Start Time: {start_str}")
    print(f"End Time: {end_str}")
else:
    print("No solution found.")