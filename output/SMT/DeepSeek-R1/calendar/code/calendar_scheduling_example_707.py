from z3 import Solver, Int, Or, And, Implies, sat

s = Solver()
day = Int('day')
start = Int('start')

total_time = day * 480 + start  # 480 minutes per day

# Only consider Monday (0) and Tuesday (1), Ryan can't meet Wednesday
s.add(Or(day == 0, day == 1))
s.add(start >= 0, start <= 450)  # 30 min meeting within 9:00-17:00

# Monday constraints
monday_constraints = []
# Ryan's Monday busy (minutes since 9:00)
ryan_monday_busy = [(30, 60), (120, 180), (240, 270), (390, 420)]
for s_start, s_end in ryan_monday_busy:
    monday_constraints.append(Or(start + 30 <= s_start, start >= s_end))

# Adam's Monday busy + preference (>=14:30)
adam_monday_busy = [(0, 90), (120, 210), (300, 420), (450, 480)]
for s_start, s_end in adam_monday_busy:
    monday_constraints.append(Or(start + 30 <= s_start, start >= s_end))
monday_constraints.append(start >= 330)  # 14:30 in minutes

s.add(Implies(day == 0, And(monday_constraints)))

# Tuesday constraints
tuesday_constraints = []
# Ryan's Tuesday busy
ryan_tuesday_busy = [(150, 210), (390, 420)]
for s_start, s_end in ryan_tuesday_busy:
    tuesday_constraints.append(Or(start + 30 <= s_start, start >= s_end))

# Adam's Tuesday busy
adam_tuesday_busy = [(0, 60), (90, 330), (420, 480)]
for s_start, s_end in adam_tuesday_busy:
    tuesday_constraints.append(Or(start + 30 <= s_start, start >= s_end))

s.add(Implies(day == 1, And(tuesday_constraints)))

# Find earliest possible time
s.minimize(total_time)

if s.check() == sat:
    m = s.model()
    d = m[day].as_long()
    st = m[start].as_long()
    day_name = "Monday" if d == 0 else "Tuesday"
    hours = st // 60 + 9
    minutes = st % 60
    print(f"Meeting starts on {day_name} at {hours:02d}:{minutes:02d}")
else:
    print("No suitable time found.")