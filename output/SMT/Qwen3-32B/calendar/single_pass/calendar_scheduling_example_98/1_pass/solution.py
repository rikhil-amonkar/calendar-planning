import z3

solver = z3.Solver()

start = z3.Int('start')

# Juan's constraints: start between 540 (9:00) and 930 (15:30)
solver.add(z3.And(start >= 540, start <= 930))

end = start + 30

# Juan's busy intervals
juan_busy = [[540, 630], [930, 960]]
for b_start, b_end in juan_busy:
    solver.add(z3.Or(end <= b_start, start >= b_end))

# Marilyn's busy intervals
marilyn_busy = [[660, 690], [750, 780]]
for b_start, b_end in marilyn_busy:
    solver.add(z3.Or(end <= b_start, start >= b_end))

# Ronald's busy intervals
ronald_busy = [[540, 630], [720, 750], [780, 810], [840, 990]]
for b_start, b_end in ronald_busy:
    solver.add(z3.Or(end <= b_start, start >= b_end))

if solver.check() == z3.sat:
    model = solver.model()
    start_val = model[start].as_long()
    day = "Monday"
    start_time = start_val
    end_time = start_val + 30
    # Convert to HH:MM
    def to_time_str(minutes):
        hours = minutes // 60
        mins = minutes % 60
        return f"{hours:02d}:{mins:02d}"
    start_str = to_time_str(start_time)
    end_str = to_time_str(end_time)
    print("SOLUTION:")
    print(f"Day: {day}")
    print(f"Start Time: {start_str}")
    print(f"End Time: {end_str}")
else:
    print("No solution found")