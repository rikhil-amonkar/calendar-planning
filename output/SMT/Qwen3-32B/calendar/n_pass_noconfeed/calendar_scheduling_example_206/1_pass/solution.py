import z3

def minutes_to_time_str(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

solver = z3.Solver()

S = z3.Int('S')

# Constraints on the meeting time
solver.add(S >= 870)  # Margaret's constraint: after 14:30 (870 min)
solver.add(S + 30 <= 1020)  # End by 17:00 (1020 min)

# Busy intervals for all participants
busy_intervals = [
    # Shirley
    (630, 660),  # 10:30-11:00
    (720, 750),  # 12:00-12:30
    # Jacob
    (540, 570),  # 9:00-9:30
    (600, 630),  # 10:00-10:30
    (660, 690),  # 11:00-11:30
    (750, 810),  # 12:30-13:30
    (870, 900),  # 14:30-15:00
    # Stephen
    (690, 720),  # 11:30-12:00
    (750, 780),  # 12:30-13:00
    # Margaret
    (540, 570),  # 9:00-9:30
    (630, 750),  # 10:30-12:30
    (780, 810),  # 13:00-13:30
    (900, 930),  # 15:00-15:30
    (990, 1020), # 16:30-17:00
    # Mason
    (540, 600),  # 9:00-10:00
    (630, 660),  # 10:30-11:00
    (690, 750),  # 11:30-12:30
    (780, 810),  # 13:00-13:30
    (840, 870),  # 14:00-14:30
    (990, 1020), # 16:30-17:00
]

# Add no-overlap constraints for each busy interval
for b_start, b_end in busy_intervals:
    solver.add(z3.Or(S + 30 <= b_start, S >= b_end))

if solver.check() == z3.sat:
    model = solver.model()
    start = model[S].as_long()
    end = start + 30
    start_str = minutes_to_time_str(start)
    end_str = minutes_to_time_str(end)
    print(f"{start_str}:{end_str} Monday")
else:
    print("No solution found")