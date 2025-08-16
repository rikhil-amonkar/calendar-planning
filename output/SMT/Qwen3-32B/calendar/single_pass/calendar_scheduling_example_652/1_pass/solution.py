import z3

def to_time_str(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

# Define busy intervals in minutes since midnight
mon_jesse = [(13*60 + 30, 14*60), (14*60 + 30, 15*60)]
tue_jesse = [(9*60, 9*60 + 30), (13*60, 13*60 + 30), (14*60, 15*60)]
mon_lawrence = [(9*60, 17*60)]
tue_lawrence = [(9*60 + 30, 10*60 + 30), (11*60 + 30, 12*60 + 30), (13*60, 13*60 + 30), (14*60 + 30, 15*60), (15*60 + 30, 16*60 + 30)]

s = z3.Solver()

day = z3.Int('day')
start = z3.Int('start')

s.add(z3.Or(day == 0, day == 1))
s.add(start >= 9*60)  # 9:00 AM
s.add(z3.If(day == 0, start <= 17*60 - 30, start <= 16*60))  # 16:00 for Tuesday

# Jesse's constraints
for b_start, b_end in mon_jesse:
    cond = z3.Implies(day == 0, z3.Or(start + 30 <= b_start, start >= b_end))
    s.add(cond)

for b_start, b_end in tue_jesse:
    cond = z3.Implies(day == 1, z3.Or(start + 30 <= b_start, start >= b_end))
    s.add(cond)

# Lawrence's constraints
for b_start, b_end in mon_lawrence:
    cond = z3.Implies(day == 0, z3.Or(start + 30 <= b_start, start >= b_end))
    s.add(cond)

for b_start, b_end in tue_lawrence:
    cond = z3.Implies(day == 1, z3.Or(start + 30 <= b_start, start >= b_end))
    s.add(cond)

if s.check() == z3.sat:
    model = s.model()
    day_val = model[day].as_long()
    start_val = model[start].as_long()
    end_val = start_val + 30
    day_str = "Monday" if day_val == 0 else "Tuesday"
    print(f"SOLUTION:")
    print(f"Day: {day_str}")
    print(f"Start Time: {to_time_str(start_val)}")
    print(f"End Time: {to_time_str(end_val)}")
else:
    print("No solution found.")