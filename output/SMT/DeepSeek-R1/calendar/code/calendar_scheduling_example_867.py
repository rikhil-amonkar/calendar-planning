from z3 import *

s = Optimize()
day = Int('day')
start = Int('start')

# Days: 2=Wednesday, 3=Thursday
s.add(Or(day == 2, day == 3))

# Wednesday constraints
s.add(Implies(day == 2, And(start >= 0, start + 30 <= 480)))

# Betty's Wednesday busy: 30-90, 240-270, 300-330
s.add(Implies(day == 2, Or(start + 30 <= 30, start >= 90)))
s.add(Implies(day == 2, Or(start + 30 <= 240, start >= 270)))
s.add(Implies(day == 2, Or(start + 30 <= 300, start >= 330)))

# Scott's Wednesday busy: 30-210, 240-270, 300-330, 360-390, 420-450
s.add(Implies(day == 2, Or(start + 30 <= 30, start >= 210)))
s.add(Implies(day == 2, Or(start + 30 <= 240, start >= 270)))
s.add(Implies(day == 2, Or(start + 30 <= 300, start >= 330)))
s.add(Implies(day == 2, Or(start + 30 <= 360, start >= 390)))
s.add(Implies(day == 2, Or(start + 30 <= 420, start >= 450)))

# Thursday constraints (start >= 360, end <= 480)
s.add(Implies(day == 3, And(start >= 360, start + 30 <= 480)))

# Betty's Thursday busy after 15:00: 360-390, 450-480
s.add(Implies(day == 3, Or(start + 30 <= 360, start >= 390)))
s.add(Implies(day == 3, Or(start + 30 <= 450, start >= 480)))

# Scott's Thursday busy after 15:00: 360-420, 450-480
s.add(Implies(day == 3, Or(start + 30 <= 360, start >= 420)))
s.add(Implies(day == 3, Or(start + 30 <= 450, start >= 480)))

# Minimize Wednesday preference and start time
s.minimize(If(day == 2, 1000, 0) + start)

if s.check() == sat:
    model = s.model()
    d = model[day].as_long()
    st = model[start].as_long()
    day_str = "Wednesday" if d == 2 else "Thursday"
    hours = 9 + st // 60
    minutes = st % 60
    print(f"Meeting can be scheduled on {day_str} at {hours:02d}:{minutes:02d}")
else:
    print("No valid time found.")