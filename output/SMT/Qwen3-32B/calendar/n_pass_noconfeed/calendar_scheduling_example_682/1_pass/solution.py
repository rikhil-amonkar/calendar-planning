import z3

solver = z3.Solver()

day = z3.Int('day')
start = z3.Int('start')

# Constraints for the day and time range
solver.add(day == 1)  # Tuesday is day 1
solver.add(start >= 540)  # 9:00 AM
solver.add(start + 30 <= 660)  # End by 11:00 AM

# Amanda's busy times on Tuesday (minutes since midnight)
amanda_busy = [(540, 570), (600, 630)]
for b_start, b_end in amanda_busy:
    solver.add(z3.Or(start + 30 <= b_start, start >= b_end))

# Nathan's busy times on Tuesday
nathan_busy = [(540, 630)]
for b_start, b_end in nathan_busy:
    solver.add(z3.Or(start + 30 <= b_start, start >= b_end))

if solver.check() == z3.sat:
    model = solver.model()
    start_val = model[start].as_long()
    end_val = start_val + 30
    day_val = model[day].as_long()
    
    # Convert start and end times to HH:MM format
    def to_time(minutes):
        h, m = divmod(minutes, 60)
        return f"{h:02d}:{m:02d}"
    
    day_str = "Tuesday" if day_val == 1 else "Monday"
    time_str = f"{to_time(start_val)}:{to_time(end_val)}"
    print(f"{day_str} {time_str}")
else:
    print("No solution found")