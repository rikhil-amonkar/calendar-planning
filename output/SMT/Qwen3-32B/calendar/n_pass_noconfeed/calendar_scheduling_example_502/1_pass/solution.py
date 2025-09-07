import z3

solver = z3.Solver()

start_time = z3.Int('start_time')

# Work hours from 9:00 (540) to 17:00 (1020), meeting is 30 min
solver.add(start_time >= 540)
solver.add(start_time + 30 <= 1020)  # end_time <= 1020
# Jack's preference: start <= 12:00 (720)
solver.add(start_time <= 720)

# Jack's busy intervals (converted to minutes since midnight)
jack_busy = [
    (570, 630),  # 9:30-10:30
    (660, 690),  # 11:00-11:30
    (750, 780),  # 12:30-13:00
    (840, 870),  # 14:00-14:30
    (960, 990),  # 16:00-16:30
]

for b_start, b_end in jack_busy:
    solver.add(z3.Or(start_time + 30 <= b_start, start_time >= b_end))

# Charlotte's busy intervals (converted to minutes since midnight)
charlotte_busy = [
    (570, 600),  # 9:30-10:00
    (630, 720),  # 10:30-12:00
    (750, 810),  # 12:30-13:30
    (840, 960),  # 14:00-16:00
]

for b_start, b_end in charlotte_busy:
    solver.add(z3.Or(start_time + 30 <= b_start, start_time >= b_end))

if solver.check() == z3.sat:
    model = solver.model()
    start = model[start_time].as_long()
    end = start + 30
    day = "Monday"
    # Convert minutes to HH:MM format
    def to_time(minutes):
        h = minutes // 60
        m = minutes % 60
        return f"{h:02d}:{m:02d}"
    start_time_str = to_time(start)
    end_time_str = to_time(end)
    print(f"{{{start_time_str}:{end_time_str}}} {day}")
else:
    print("No solution found")