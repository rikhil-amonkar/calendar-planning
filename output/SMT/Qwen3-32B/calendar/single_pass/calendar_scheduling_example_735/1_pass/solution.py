from z3 import *

# Define the days and blocked intervals for Ronald and Amber
ronald_blocked = [
    # Monday
    [(630, 660), (720, 750), (930, 960)],
    # Tuesday
    [(540, 570), (720, 750), (930, 990)],
    # Wednesday
    [(570, 630), (660, 720), (750, 780), (810, 840), (990, 1020)],
]

amber_blocked = [
    # Monday
    [(540, 570), (600, 630), (690, 720), (750, 840), (870, 900), (930, 1020)],
    # Tuesday
    [(540, 570), (600, 690), (720, 750), (810, 930), (990, 1020)],
    # Wednesday
    [(540, 570), (600, 630), (660, 810), (900, 930)],
]

# Create Z3 variables
day = Int('day')
start = Int('start')

opt = Optimize()

# Add constraints for day and start time
opt.add(And(day >= 0, day <= 2))
opt.add(And(start >= 540, start <= 990))

# For each day, generate constraints based on blocked intervals
for d in range(3):
    ronald_intervals = ronald_blocked[d]
    amber_intervals = amber_blocked[d]
    
    # Generate constraints for Ronald's blocked intervals
    ronald_conds = []
    for s, e in ronald_intervals:
        ronald_conds.append(Or(start + 30 <= s, start >= e))
    ronald_constraints = And(ronald_conds)
    
    # Generate constraints for Amber's blocked intervals
    amber_conds = []
    for s, e in amber_intervals:
        amber_conds.append(Or(start + 30 <= s, start >= e))
    amber_constraints = And(amber_conds)
    
    # Combine constraints for the day
    day_constraints = And(ronald_constraints, amber_constraints)
    
    # Add implication: if day == d, then day_constraints must hold
    opt.add(Implies(day == d, day_constraints))

# Minimize the start time to find the earliest possible meeting
opt.minimize(start)

# Check for a solution
if opt.check() == sat:
    model = opt.model()
    day_val = model[day].as_long()
    start_val = model[start].as_long()
    end_val = start_val + 30
    days = ['Monday', 'Tuesday', 'Wednesday']
    print("SOLUTION:")
    print(f"Day: {days[day_val]}")
    print(f"Start Time: {start_val // 60:02d}:{start_val % 60:02d}")
    print(f"End Time: {end_val // 60:02d}:{end_val % 60:02d}")
else:
    print("No solution found.")