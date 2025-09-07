from z3 import *

# Define variables
day = Int('day')
start = Int('start')

opt = Optimize()

# Constraints on day and start
opt.add(And(day >= 0, day <= 2))
opt.add(And(start >= 0, start <= 420))

# Busy intervals for each day (Monday, Tuesday, Wednesday)
busy_intervals = [
    # Monday: 10:00-11:30, 12:00-13:00, 14:00-14:30, 15:00-17:00
    [(60, 150), (180, 240), (300, 330), (360, 480)],
    # Tuesday: 10:30-11:30, 12:00-14:30, 15:00-15:30, 16:00-17:00
    [(90, 150), (180, 330), (360, 390), (420, 480)],
    # Wednesday: 9:30-11:30, 12:30-14:00, 14:30-15:30, 16:30-17:00
    [(30, 150), (210, 300), (330, 390), (450, 480)]
]

# Add constraints for each busy interval
for d in range(3):
    for b_start, b_end in busy_intervals[d]:
        opt.add(Implies(day == d, Or(start + 60 <= b_start, start >= b_end)))

# Objective: minimize day * 1000 + start to prioritize earliest day and time
opt.minimize(day * 1000 + start)

# Check solution
if opt.check() == sat:
    model = opt.model()
    day_val = model[day].as_long()
    start_val = model[start].as_long()
    end_val = start_val + 60

    # Convert minutes since 9:00 to HH:MM format
    def to_time(minutes):
        hours = 9 + minutes // 60
        mins = minutes % 60
        return f"{hours:02d}:{mins:02d}"

    days_of_week = ['Monday', 'Tuesday', 'Wednesday']
    day_name = days_of_week[day_val]
    start_time = to_time(start_val)
    end_time = to_time(end_val)

    print(f"{day_name} {start_time}:{end_time}")
else:
    print("No solution found.")