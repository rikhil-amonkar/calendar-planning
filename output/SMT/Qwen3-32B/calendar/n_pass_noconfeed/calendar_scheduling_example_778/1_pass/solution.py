import z3

solver = z3.Solver()

day = z3.Int('day')
start_time = z3.Int('start_time')

# Work hours from 9:00 to 17:00 => 0 to 450 minutes
solver.add(z3.And(day >= 0, day <= 2))
solver.add(z3.And(start_time >= 0, start_time <= 450))

# Susan's preference: not on Tuesday (day 1)
solver.add(day != 1)

# Sandra's Monday constraint: start_time <= 390
solver.add(z3.Implies(day == 0, start_time <= 390))

# Susan's blocked intervals
blocked_susan = {
    0: [(210, 240), (270, 300)],  # Monday
    1: [(150, 180)],              # Tuesday
    2: [(30, 90), (300, 330), (390, 450)]  # Wednesday
}

# Sandra's blocked intervals
blocked_sandra = {
    0: [(0, 240), (300, 360), (420, 450)],  # Monday
    1: [(0, 30), (90, 180), (210, 270), (300, 330), (420, 480)],  # Tuesday
    2: [(0, 150), (180, 210), (240, 480)]  # Wednesday
}

# Add constraints for Susan's blocked intervals
for d in range(3):
    for (b_start, b_end) in blocked_susan[d]:
        solver.add(z3.Implies(day == d, z3.Or(start_time + 30 <= b_start, start_time >= b_end)))

# Add constraints for Sandra's blocked intervals
for d in range(3):
    for (b_start, b_end) in blocked_sandra[d]:
        solver.add(z3.Implies(day == d, z3.Or(start_time + 30 <= b_start, start_time >= b_end)))

if solver.check() == z3.sat:
    model = solver.model()
    day_val = model[day].as_long()
    start_val = model[start_time].as_long()
    end_val = start_val + 30

    def to_time(mins):
        hours = 9 + mins // 60
        minutes = mins % 60
        return f"{hours:02d}:{minutes:02d}"

    day_names = ["Monday", "Tuesday", "Wednesday"]
    time_str = f"{to_time(start_val)}:{to_time(end_val)}"
    print(f"{day_names[day_val]} {time_str}")
else:
    print("No solution found")