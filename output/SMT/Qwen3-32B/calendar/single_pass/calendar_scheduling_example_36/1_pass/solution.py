import z3

solver = z3.Solver()

start = z3.Int('start')

# Work hours constraints and Denise's end time constraint
solver.add(start >= 540)  # 9:00 AM
solver.add(start <= 690)  # 11:30 AM (Denise's latest start time)

# Ryan's busy intervals
ryan_busys = [(540, 570), (750, 780)]
for b_start, b_end in ryan_busys:
    solver.add(z3.Or(start >= b_end, start + 60 <= b_start))

# Denise's busy intervals
denise_busys = [(570, 630), (720, 780), (870, 990)]
for b_start, b_end in denise_busys:
    solver.add(z3.Or(start >= b_end, start + 60 <= b_start))

if solver.check() == z3.sat:
    model = solver.model()
    start_val = model[start].as_long()
    end_val = start_val + 60

    def to_time_str(minutes):
        hours = minutes // 60
        mins = minutes % 60
        return f"{hours:02d}:{mins:02d}"

    print("SOLUTION:")
    print("Day: Monday")
    print(f"Start Time: {to_time_str(start_val)}")
    print(f"End Time: {to_time_str(end_val)}")
else:
    print("No solution found.")