import z3

def minutes_to_time(m):
    hours = m // 60
    mins = m % 60
    return f"{hours:02d}:{mins:02d}"

solver = z3.Solver()

day = z3.Int('day')
start = z3.Int('start')
end = start + 30

# Basic constraints
solver.add(z3.Or(day == 0, day == 1, day == 2))
solver.add(start >= 540, start <= 990)  # since end is start + 30 <= 1020

# Sandra can't meet on Monday after 16:00
solver.add(z3.Implies(day == 0, start <= 930))  # 16:00 is 960, start +30 <= 960 → start <= 930

# Susan's blocked intervals
susan_blocks = [
    (0, 750, 780),  # Monday 12:30-13:00
    (0, 810, 840),  # Monday 13:30-14:00
    (1, 690, 720),  # Tuesday 11:30-12:00
    (2, 570, 630),  # Wednesday 9:30-10:30
    (2, 840, 870),  # Wednesday 14:00-14:30
    (2, 930, 990),  # Wednesday 15:30-16:30
]

# Sandra's blocked intervals
sandra_blocks = [
    (0, 540, 780),   # Monday 9:00-13:00
    (0, 840, 900),   # Monday 14:00-15:00
    (0, 960, 990),   # Monday 16:00-16:30
    (1, 540, 570),   # Tuesday 9:00-9:30
    (1, 630, 720),   # Tuesday 10:30-12:00
    (1, 750, 810),   # Tuesday 12:30-13:30
    (1, 840, 870),   # Tuesday 14:00-14:30
    (1, 960, 1020),  # Tuesday 16:00-17:00
    (2, 540, 690),   # Wednesday 9:00-11:30
    (2, 720, 750),   # Wednesday 12:00-12:30
    (2, 780, 1020),  # Wednesday 13:00-17:00
]

# Add Susan's constraints
for d, s, e in susan_blocks:
    solver.add(z3.Implies(day == d, z3.Or(start + 30 <= s, start >= e)))

# Add Sandra's constraints
for d, s, e in sandra_blocks:
    solver.add(z3.Implies(day == d, z3.Or(start + 30 <= s, start >= e)))

# Try to find a solution that doesn't use Tuesday (Susan's preference)
solver.push()
solver.add(day != 1)

if solver.check() == z3.sat:
    model = solver.model()
    day_val = model.eval(day).as_long()
    start_val = model.eval(start).as_long()
    end_val = start_val + 30
    days = ['Monday', 'Tuesday', 'Wednesday']
    print("SOLUTION:")
    print(f"Day: {days[day_val]}")
    print(f"Start Time: {minutes_to_time(start_val)}")
    print(f"End Time: {minutes_to_time(end_val)}")
else:
    # Remove the preference and try again
    solver.pop()
    if solver.check() == z3.sat:
        model = solver.model()
        day_val = model.eval(day).as_long()
        start_val = model.eval(start).as_long()
        end_val = start_val + 30
        days = ['Monday', 'Tuesday', 'Wednesday']
        print("SOLUTION:")
        print(f"Day: {days[day_val]}")
        print(f"Start Time: {minutes_to_time(start_val)}")
        print(f"End Time: {minutes_to_time(end_val)}")
    else:
        print("No solution found")