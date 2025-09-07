import z3

def to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

solver = z3.Solver()

start_time = z3.Int('start_time')

# Meeting must start between 9:00 (540) and 16:30 (990)
solver.add(start_time >= 540)
solver.add(start_time + 30 <= 990)

# Eric's constraints
# Blocked: 12:00-13:00 (720-780)
solver.add(z3.Or(start_time + 30 <= 720, start_time >= 780))
# Blocked: 14:00-15:00 (840-900)
solver.add(z3.Or(start_time + 30 <= 840, start_time >= 900))

# Henry's constraints
# Blocked: 9:30-10:00 (570-600)
solver.add(z3.Or(start_time + 30 <= 570, start_time >= 600))
# Blocked: 10:30-11:00 (630-660)
solver.add(z3.Or(start_time + 30 <= 630, start_time >= 660))
# Blocked: 11:30-12:30 (690-750)
solver.add(z3.Or(start_time + 30 <= 690, start_time >= 750))
# Blocked: 13:00-13:30 (780-810)
solver.add(z3.Or(start_time + 30 <= 780, start_time >= 810))
# Blocked: 14:30-15:00 (870-900)
solver.add(z3.Or(start_time + 30 <= 870, start_time >= 900))
# Blocked: 16:00-17:00 (960-1020)
solver.add(z3.Or(start_time + 30 <= 960, start_time >= 1020))

# Henry's preference: not after 10:00
solver.add(start_time <= 570)

if solver.check() == z3.sat:
    model = solver.model()
    st = model[start_time].as_long()
    end_time = st + 30
    start_str = to_time(st)
    end_str = to_time(end_time)
    print(f"{start_str}:{end_str} Monday")
else:
    # Remove the preference and try again
    solver = z3.Solver()
    start_time = z3.Int('start_time')
    solver.add(start_time >= 540)
    solver.add(start_time + 30 <= 990)
    # Eric's constraints
    solver.add(z3.Or(start_time + 30 <= 720, start_time >= 780))
    solver.add(z3.Or(start_time + 30 <= 840, start_time >= 900))
    # Henry's constraints
    solver.add(z3.Or(start_time + 30 <= 570, start_time >= 600))
    solver.add(z3.Or(start_time + 30 <= 630, start_time >= 660))
    solver.add(z3.Or(start_time + 30 <= 690, start_time >= 750))
    solver.add(z3.Or(start_time + 30 <= 780, start_time >= 810))
    solver.add(z3.Or(start_time + 30 <= 870, start_time >= 900))
    solver.add(z3.Or(start_time + 30 <= 960, start_time >= 1020))
    if solver.check() == z3.sat:
        model = solver.model()
        st = model[start_time].as_long()
        end_time = st + 30
        start_str = to_time(st)
        end_str = to_time(end_time)
        print(f"{start_str}:{end_str} Monday")
    else:
        print("No solution found")