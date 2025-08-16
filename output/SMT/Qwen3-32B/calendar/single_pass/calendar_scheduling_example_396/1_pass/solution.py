import z3

solver = z3.Solver()

t = z3.Int('t')

solver.add(t >= 9 * 60)  # 540 (09:00)
solver.add(t <= 17 * 60 - 30)  # 990 (16:30)

# Busy intervals (start, end in minutes since midnight)
busy_intervals = [
    # Jack's intervals
    (540, 570),  # 09:00-09:30
    (840, 870),  # 14:00-14:30
    # Madison's intervals
    (570, 630),  # 09:30-10:30
    (780, 840),  # 13:00-14:00
    (900, 930),  # 15:00-15:30
    (990, 1020),  # 16:30-17:00
    # Rachel's intervals
    (570, 630),  # 09:30-10:30
    (660, 690),  # 11:00-11:30
    (720, 810),  # 12:00-13:30
    (870, 930),  # 14:30-15:30
    (960, 1020),  # 16:00-17:00
    # Douglas's intervals
    (540, 690),  # 09:00-11:30
    (720, 990),  # 12:00-16:30
    # Ryan's intervals
    (540, 570),  # 09:00-09:30
    (780, 840),  # 13:00-14:00
    (870, 1020),  # 14:30-17:00
]

for start, end in busy_intervals:
    solver.add(z3.Or(t + 30 <= start, t >= end))

if solver.check() == z3.sat:
    model = solver.model()
    t_val = model[t].as_long()
    
    def to_time_str(minutes):
        hours = minutes // 60
        mins = minutes % 60
        return f"{hours:02d}:{mins:02d}"
    
    day = "Monday"
    start_time = to_time_str(t_val)
    end_time = to_time_str(t_val + 30)
    print("SOLUTION:")
    print(f"Day: {day}")
    print(f"Start Time: {start_time}")
    print(f"End Time: {end_time}")
else:
    print("No solution found")