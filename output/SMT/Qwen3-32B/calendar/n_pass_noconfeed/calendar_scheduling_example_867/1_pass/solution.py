import z3

s = z3.Solver()

day = z3.Int('day')
start_time = z3.Int('start_time')

# Day can be 0 (Tuesday), 1 (Wednesday), 2 (Thursday)
s.add(z3.Or(day == 0, day == 1, day == 2))

# Betty's constraints: on Tuesday (0) and Thursday (2), start_time >= 360 (15:00)
s.add(z3.Implies(day == 0, start_time >= 360))
s.add(z3.Implies(day == 2, start_time >= 360))

# Work hours: start_time + 30 <= 480 (17:00)
s.add(start_time + 30 <= 480)

# Betty's busy times per day
betty_busy = {
    0: [(0, 30), (150, 180), (210, 240), (270, 300), (450, 480)],
    1: [(90, 150), (240, 270), (300, 330)],
    2: [(90, 120), (150, 180), (300, 330), (360, 390), (450, 480)]
}

# Scott's busy times per day
scott_busy = {
    0: [(0, 30), (60, 120), (150, 180), (210, 270), (300, 360), (420, 450)],
    1: [(90, 270), (240, 270), (300, 330), (360, 390), (420, 450), (450, 480)],
    2: [(0, 30), (60, 90), (180, 240), (240, 270), (360, 420), (450, 480)]
}

# Add constraints for Betty's busy times
for d in [0, 1, 2]:
    for b_start, b_end in betty_busy[d]:
        overlap = z3.And(day == d, start_time < b_end, start_time + 30 > b_start)
        s.add(z3.Not(overlap))

# Add constraints for Scott's busy times
for d in [0, 1, 2]:
    for b_start, b_end in scott_busy[d]:
        overlap = z3.And(day == d, start_time < b_end, start_time + 30 > b_start)
        s.add(z3.Not(overlap))

if s.check() == z3.sat:
    model = s.model()
    day_val = model[day].as_long()
    start_val = model[start_time].as_long()

    def minutes_to_time(minutes_since_9):
        total_minutes = minutes_since_9
        hours = 9 + total_minutes // 60
        mins = total_minutes % 60
        return f"{hours:02d}:{mins:02d}"

    start_str = minutes_to_time(start_val)
    end_str = minutes_to_time(start_val + 30)
    day_names = ['Tuesday', 'Wednesday', 'Thursday']
    day_name = day_names[day_val]
    print(f"{day_name} {start_str}:{end_str}")
else:
    print("No solution found")