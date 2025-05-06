from z3 import *

s = Optimize()

day = Int('day')
start_time = Int('start_time')

s.add(Or(day == 0, day == 2))
s.add(start_time >= 0)
s.add(start_time <= 450)

arthur_schedule = {
    0: [(120, 150), (270, 300), (360, 390)],
    2: [(60, 90), (120, 150), (180, 210), (300, 330), (420, 450)]
}

michael_schedule = {
    0: [(0, 180), (210, 240), (300, 330), (360, 480)],
    2: [(60, 210), (240, 270)]
}

def add_conflicts(schedule, person_day):
    for meeting in schedule.get(person_day, []):
        s_start, s_end = meeting
        s.add(Implies(day == person_day,
                      Or(start_time + 30 <= s_start,
                         start_time >= s_end)))

for d in [0, 2]:
    add_conflicts(arthur_schedule, d)
for d in [0, 2]:
    add_conflicts(michael_schedule, d)

s.minimize(day * 1000 + start_time)

if s.check() == sat:
    m = s.model()
    d = m[day].as_long()
    st = m[start_time].as_long()
    days = ['Monday', 'Tuesday', 'Wednesday']
    start_h = 9 + st // 60
    start_m = st % 60
    end_h = 9 + (st + 30) // 60
    end_m = (st + 30) % 60
    print(f"{days[d]} {start_h:02d}:{start_m:02d}-{end_h:02d}:{end_m:02d}")
else:
    print("No solution found")