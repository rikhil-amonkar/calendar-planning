from z3 import *

def to_time(minutes_since_9):
    total = minutes_since_9
    hours = total // 60
    mins = total % 60
    hour_24 = 9 + hours
    return f"{hour_24:02d}:{mins:02d}"

s = Solver()

day = Int('day')
start = Int('start')

s.add(Or(day == 2, day == 4))
s.add(And(start >= 0, start <= 420))

# Bryan's constraints on Friday
bryan_friday_busy = [(90, 120), (300, 330)]
for b_start, b_end in bryan_friday_busy:
    s.add(Implies(day == 4, Or(start >= b_end, start + 60 <= b_start)))

# Nicholas's constraints on Wednesday
nicholas_wed_busy = [(0, 30), (60, 120), (150, 270), (300, 330), (360, 450)]
for n_start, n_end in nicholas_wed_busy:
    s.add(Implies(day == 2, Or(start >= n_end, start + 60 <= n_start)))

# Nicholas's constraints on Friday
nicholas_fri_busy = [(0, 90), (120, 180), (210, 330), (390, 420), (450, 480)]
for n_start, n_end in nicholas_fri_busy:
    s.add(Implies(day == 4, Or(start >= n_end, start + 60 <= n_start)))

if s.check() == sat:
    m = s.model()
    day_val = m[day].as_long()
    start_val = m[start].as_long()
    days = ['Monday', 'Tuesday', 'Wednesday', 'Thursday', 'Friday']
    day_name = days[day_val]
    start_time = to_time(start_val)
    end_time = to_time(start_val + 60)
    print(f"SOLUTION:\nDay: {day_name}\nStart Time: {start_time}\nEnd Time: {end_time}")
else:
    print("No solution found")