import z3

solver = z3.Solver()

t = z3.Int('t')

# Define work hours (9:00 to 17:00) and meeting duration (30 minutes)
solver.add(t >= 9 * 60)
solver.add(t <= 17 * 60 - 30)

# Adam's busy times: 14:00-15:00
adam_busy = [[14 * 60, 15 * 60]]
for start, end in adam_busy:
    solver.add(z3.Or(t + 30 <= start, t >= end))

# John's busy times: 13:00-13:30, 14:00-14:30, 15:30-16:00, 16:30-17:00
john_busy = [
    [13 * 60, 13 * 60 + 30],
    [14 * 60, 14 * 60 + 30],
    [15 * 60 + 30, 16 * 60],
    [16 * 60 + 30, 17 * 60]
]
for start, end in john_busy:
    solver.add(z3.Or(t + 30 <= start, t >= end))

# Stephanie's busy times: 9:30-10:00, 10:30-11:00, 11:30-16:00, 16:30-17:00
stephanie_busy = [
    [9 * 60 + 30, 10 * 60],
    [10 * 60 + 30, 11 * 60],
    [11 * 60 + 30, 16 * 60],
    [16 * 60 + 30, 17 * 60]
]
for start, end in stephanie_busy:
    solver.add(z3.Or(t + 30 <= start, t >= end))

# Anna's busy times: 9:30-10:00, 12:00-12:30, 13:00-15:30, 16:30-17:00
anna_busy = [
    [9 * 60 + 30, 10 * 60],
    [12 * 60, 12 * 60 + 30],
    [13 * 60, 15 * 60 + 30],
    [16 * 60 + 30, 17 * 60]
]
for start, end in anna_busy:
    solver.add(z3.Or(t + 30 <= start, t >= end))

# Anna's preference: not before 14:30
solver.add(t >= 14 * 60 + 30)

if solver.check() == z3.sat:
    model = solver.model()
    t_val = model[t].as_long()
    start_h = t_val // 60
    start_m = t_val % 60
    end_h = (t_val + 30) // 60
    end_m = (t_val + 30) % 60
    start_time = f"{start_h}:{start_m:02d}"
    end_time = f"{end_h}:{end_m:02d}"
    print(f"Monday {{{start_time}:{end_time}}}")
else:
    print("No solution found")