import z3

solver = z3.Solver()

day = z3.Int('day')
start = z3.Int('start')
end = start + 60

solver.add(z3.And(0 <= day, day <= 4))
solver.add(z3.And(0 <= start, start <= 420))  # since end is start+60 <= 480

# Bryan's busy times
bryan_busy = {
    0: [],  # Monday
    1: [],   # Tuesday
    2: [],   # Wednesday
    3: [(30, 60), (210, 240)],  # Thursday
    4: [(90, 120), (240, 270)]  # Friday
}

# Nicholas's busy times
nicholas_busy = {
    0: [(150, 180), (240, 390), (300, 450)],  # Monday
    1: [(0, 30), (120, 270), (300, 450)],  # Tuesday
    2: [(0, 30), (60, 120), (150, 270), (300, 330), (360, 450)],  # Wednesday
    3: [(90, 150), (180, 210), (360, 390), (450, 480)],  # Thursday
    4: [(0, 90), (120, 180), (210, 330), (390, 420), (450, 480)]  # Friday
}

# Add constraints for each day's busy times
for d in range(5):
    for s_b, e_b in bryan_busy[d]:
        solver.add(z3.Or(day != d, start >= e_b, start + 60 <= s_b))
    for s_n, e_n in nicholas_busy[d]:
        solver.add(z3.Or(day != d, start >= e_n, start + 60 <= s_n))

# Try to find a solution that is not on Monday, Tuesday, or Thursday
solver.push()
solver.add(z3.Or(day == 2, day == 4))  # day is Wednesday or Friday

if solver.check() == z3.sat:
    model = solver.model()
    day_val = model[day].as_long()
    start_val = model[start].as_long()
    days = ["Monday", "Tuesday", "Wednesday", "Thursday", "Friday"]
    day_name = days[day_val]
    def to_time(minutes):
        total = minutes
        hours = 9 + total // 60
        mins = total % 60
        return f"{hours:02d}:{mins:02d}"
    start_time = to_time(start_val)
    end_time = to_time(start_val + 60)
    print(f"{day_name} {start_time}:{end_time}")
else:
    solver.pop()
    # Try without the preference constraints
    if solver.check() == z3.sat():
        model = solver.model()
        day_val = model[day].as_long()
        start_val = model[start].as_long()
        days = ["Monday", "Tuesday", "Wednesday", "Thursday", "Friday"]
        day_name = days[day_val]
        def to_time(minutes):
            total = minutes
            hours = 9 + total // 60
            mins = total % 60
            return f"{hours:02d}:{mins:02d}"
        start_time = to_time(start_val)
        end_time = to_time(start_val + 60)
        print(f"{day_name} {start_time}:{end_time}")
    else:
        print("No solution found")