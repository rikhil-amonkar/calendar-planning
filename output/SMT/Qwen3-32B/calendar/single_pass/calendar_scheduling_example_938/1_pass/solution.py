from z3 import *

# Define busy intervals for each person and day
eugene_busy = {
    0: [(660, 720), (810, 840), (870, 900), (960, 990)],
    1: [],
    2: [(540, 570), (660, 690), (720, 750), (810, 900)],
    3: [(570, 600), (660, 750)],
    4: [(630, 660), (720, 750), (780, 810)],
}

eric_busy = {
    0: [(540, 1020)],
    1: [(540, 1020)],
    2: [(540, 690), (720, 840), (870, 990)],
    3: [(540, 1020)],
    4: [(540, 660), (690, 1020)],
}

def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

solver = Solver()

d = Int('d')
st = Int('st')

# Add constraints for day and time
solver.add(And(d >= 0, d <= 4))
solver.add(And(st >= 540, st <= 990))

# Add constraints for busy intervals
for D in range(5):
    intervals = eugene_busy[D] + eric_busy[D]
    for (s, e) in intervals:
        # If day is D, then the meeting time does not overlap with (s, e)
        c = Implies(d == D, Or(st + 30 <= s, st >= e))
        solver.add(c)

# Try to find a solution that's not on Wednesday (d != 2)
solver.push()
solver.add(d != 2)

if solver.check() == sat:
    model = solver.model()
    day_val = model[d].as_long()
    st_val = model[st].as_long()
    end_val = st_val + 30
    # Output
    days = ["Monday", "Tuesday", "Wednesday", "Thursday", "Friday"]
    day_name = days[day_val]
    print("SOLUTION:")
    print(f"Day: {day_name}")
    print(f"Start Time: {minutes_to_time(st_val)}")
    print(f"End Time: {minutes_to_time(end_val)}")
else:
    # No solution without Wednesday, try with Wednesday
    solver.pop()
    if solver.check() == sat:
        model = solver.model()
        day_val = model[d].as_long()
        st_val = model[st].as_long()
        end_val = st_val + 30
        days = ["Monday", "Tuesday", "Wednesday", "Thursday", "Friday"]
        day_name = days[day_val]
        print("SOLUTION:")
        print(f"Day: {day_name}")
        print(f"Start Time: {minutes_to_time(st_val)}")
        print(f"End Time: {minutes_to_time(end_val)}")
    else:
        print("No solution found.")