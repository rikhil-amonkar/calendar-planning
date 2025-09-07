from z3 import *

s = Solver()

day = Int('day')
start = Int('start')

s.add(Or(day == 0, day == 1, day == 2))
s.add(And(0 <= start, start <= 450))

# John's constraint on Monday (14:30 is 330 minutes after 9:00)
s.add(Implies(day == 0, start + 30 <= 330))

# Jennifer's busy intervals
# Monday: 9:00-11:00 (0-120), 11:30-13:00 (150-240), 13:30-14:30 (270-330), 15:00-17:00 (360-480)
mon_busy = [(0, 120), (150, 240), (270, 330), (360, 480)]
for a, b in mon_busy:
    s.add(Implies(day == 0, Or(start + 30 <= a, start >= b)))

# Tuesday: 9:00-11:30 (0-150), 12:00-17:00 (180-480)
tue_busy = [(0, 150), (180, 480)]
for a, b in tue_busy:
    s.add(Implies(day == 1, Or(start + 30 <= a, start >= b)))

# Wednesday: 9:00-11:30 (0-150), 12:00-12:30 (180-210), 13:00-14:00 (240-300), 14:30-16:00 (330-420), 16:30-17:00 (450-480)
wed_busy = [(0, 150), (180, 210), (240, 300), (330, 420), (450, 480)]
for a, b in wed_busy:
    s.add(Implies(day == 2, Or(start + 30 <= a, start >= b)))

if s.check() == sat:
    model = s.model()
    d = model[day].as_long()
    st = model[start].as_long()
    days = ['Monday', 'Tuesday', 'Wednesday']
    day_name = days[d]
    start_h = 9 + st // 60
    start_m = st % 60
    end_h = 9 + (st + 30) // 60
    end_m = (st + 30) % 60
    time_str = f"{start_h:02d}:{start_m:02d}:{end_h:02d}:{end_m:02d}"
    print(f"{time_str} {day_name}")
else:
    print("No solution")