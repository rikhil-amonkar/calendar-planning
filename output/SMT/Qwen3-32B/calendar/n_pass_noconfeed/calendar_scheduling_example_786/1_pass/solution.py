import z3

s = z3.Solver()

day = z3.Int('day')
start_time = z3.Int('start_time')

# Day must be Monday (0), Tuesday (1), or Wednesday (2)
s.add(z3.Or(day == 0, day == 1, day == 2))

# Start time between 9:00 (540) and 16:30 (990)
s.add(z3.And(start_time >= 540, start_time <= 990))

# Amy's constraints: only on Wednesday (day == 2)
amy_constraints = []
amy_constraints.append(z3.Implies(day == 2, z3.Or(start_time + 30 <= 660, start_time >= 690)))
amy_constraints.append(z3.Implies(day == 2, z3.Or(start_time + 30 <= 810, start_time >= 840)))
s.add(amy_constraints)

# Pamela's constraints
pamela_constraints = []

# Monday (day 0)
pamela_monday = z3.Implies(day == 0, z3.Or(
    start_time + 30 <= 540, 
    z3.And(start_time >= 630, start_time + 30 <= 660), 
    start_time >= 990
))
pamela_constraints.append(pamela_monday)

# Tuesday (day 1)
pamela_tuesday = z3.Implies(day == 1, z3.Or(
    start_time + 30 <= 540, 
    z3.And(start_time >= 570, start_time + 30 <= 600), 
    start_time >= 1020  # which is beyond 990, so redundant
))
pamela_constraints.append(pamela_tuesday)

# Wednesday (day 2)
pamela_wednesday = z3.Implies(day == 2, z3.And(
    z3.Or(start_time + 30 <= 540, start_time >= 570),  # 540-570
    z3.Or(start_time + 30 <= 600, start_time >= 660),  # 600-660
    z3.Or(start_time + 30 <= 690, start_time >= 810),  # 690-810
    z3.Or(start_time + 30 <= 870, start_time >= 900),  # 870-900
    z3.Or(start_time + 30 <= 960, start_time >= 990)   # 960-990
))
pamela_constraints.append(pamela_wednesday)

s.add(pamela_constraints)

# Add preference for Wednesday after 16:00 (960 minutes)
s.add(z3.And(day == 2, start_time >= 960))

if s.check() == z3.sat:
    m = s.model()
    d = m[day].as_long()
    st = m[start_time].as_long()
    days = ['Monday', 'Tuesday', 'Wednesday']
    day_name = days[d]
    # Convert start time to HH:MM
    start_h = st // 60
    start_m = st % 60
    start_str = f"{start_h:02d}:{start_m:02d}"
    end_time = st + 30
    end_h = end_time // 60
    end_m = end_time % 60
    end_str = f"{end_h:02d}:{end_m:02d}"
    print(f"{start_str}:{end_str} {day_name}")
else:
    print("No solution found")