from z3 import *

def minutes_to_time(m):
    hours = m // 60
    mins = m % 60
    return f"{hours:02d}:{mins:02d}"

solver = Solver()

day = Int('day')
start = Int('start')

# Basic constraints
solver.add(Or(day == 0, day == 1, day == 2))
solver.add(And(start >= 540, start <= 990))

# John's Monday constraint
solver.add(Implies(day == 0, start <= 840))  # 14:00

# Add Jennifer's constraints
def add_jennifer_constraints(solver, day_var, start_var):
    # Monday's busy intervals
    mon_busy = [
        (540, 660),   # 9:00-11:00
        (690, 780),   # 11:30-13:00
        (810, 870),   # 13:30-14:30
        (900, 1020),  # 15:00-17:00
    ]
    # Tuesday's busy intervals
    tue_busy = [
        (540, 690),   # 9:00-11:30
        (720, 1020),  # 12:00-17:00
    ]
    # Wednesday's busy intervals
    wed_busy = [
        (540, 690),   # 9:00-11:30
        (720, 750),   # 12:00-12:30
        (780, 840),   # 13:00-14:00
        (870, 960),   # 14:30-16:00
        (990, 1020),  # 16:30-17:00
    ]

    for d in range(3):
        busy_intervals = []
        if d == 0:
            busy_intervals = mon_busy
        elif d == 1:
            busy_intervals = tue_busy
        else:
            busy_intervals = wed_busy

        for (b_start, b_end) in busy_intervals:
            cond = (day_var == d)
            constraint = Implies(cond, Or(start_var + 30 <= b_start, start_var >= b_end))
            solver.add(constraint)

add_jennifer_constraints(solver, day, start)

if solver.check() == sat:
    model = solver.model()
    day_val = model[day].as_long()
    start_val = model[start].as_long()
    end_val = start_val + 30
    days = ['Monday', 'Tuesday', 'Wednesday']
    print("SOLUTION:")
    print(f"Day: {days[day_val]}")
    print(f"Start Time: {minutes_to_time(start_val)}")
    print(f"End Time: {minutes_to_time(end_val)}")
else:
    print("No solution found.")