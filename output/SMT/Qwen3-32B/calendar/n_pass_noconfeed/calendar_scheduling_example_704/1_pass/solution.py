from z3 import *

def minutes(time_str):
    h, m = map(int, time_str.split(':'))
    return h * 60 + m

# Existing meetings for Samuel
meetings_monday = [
    (minutes("10:30"), minutes("11:00")),
    (minutes("12:00"), minutes("12:30")),
    (minutes("13:00"), minutes("15:00")),
    (minutes("15:30"), minutes("16:30"))
]

meetings_tuesday = [
    (minutes("9:00"), minutes("12:00")),
    (minutes("14:00"), minutes("15:30")),
    (minutes("16:30"), minutes("17:00"))
]

meetings_wednesday = [
    (minutes("10:30"), minutes("11:00")),
    (minutes("11:30"), minutes("12:00")),
    (minutes("12:30"), minutes("13:00")),
    (minutes("14:00"), minutes("14:30")),
    (minutes("15:00"), minutes("16:00"))
]

# Variables
day = Int('day')
start_time = Int('start_time')

s = Optimize()

# Constraints for day and time
s.add(Or(day == 0, day == 1, day == 2))
s.add(start_time >= 540)  # 9:00 AM
s.add(start_time + 30 <= 1020)  # 5:00 PM

# Add constraints for Samuel's existing meetings
for a, b in meetings_monday:
    s.add(Implies(day == 0, Or(start_time + 30 <= a, start_time >= b)))

for a, b in meetings_tuesday:
    s.add(Implies(day == 1, Or(start_time + 30 <= a, start_time >= b)))

for a, b in meetings_wednesday:
    s.add(Implies(day == 2, Or(start_time + 30 <= a, start_time >= b)))

# Optimization objectives: minimize day, then start_time
s.minimize(day)
s.minimize(start_time)

if s.check() == sat:
    model = s.model()
    day_val = model[day].as_long()
    start_val = model[start_time].as_long()
    end_val = start_val + 30

    # Convert day to name
    days = ["Monday", "Tuesday", "Wednesday"]
    day_name = days[day_val]

    # Convert start and end times to HH:MM
    def to_time(mins):
        h = mins // 60
        m = mins % 60
        return f"{h:02d}:{m:02d}"

    start_time_str = to_time(start_val)
    end_time_str = to_time(end_val)
    print(f"{{{start_time_str}:{end_time_str}}}")
    print(day_name)
else:
    print("No solution")