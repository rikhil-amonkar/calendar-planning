from z3 import *

# Define busy times for each day in minutes since midnight
busy_mon = [
    (600, 690),  # 10:00-11:30
    (720, 780),  # 12:00-13:00
    (840, 870),  # 14:00-14:30
    (900, 1020)  # 15:00-17:00
]

busy_tue = [
    (630, 690),   # 10:30-11:30
    (720, 870),   # 12:00-14:30
    (900, 930),   # 15:00-15:30
    (960, 1020)   # 16:00-17:00
]

busy_wed = [
    (570, 690),   # 09:30-11:30
    (750, 840),   # 12:30-14:00
    (870, 930),   # 14:30-15:30
    (990, 1020)   # 16:30-17:00
]

opt = Optimize()

day = Int('day')
start = Int('start')

# Constraints for day and start time
opt.add(day >= 0, day <= 2)
opt.add(start >= 540, start <= 960)  # 9:00-16:00 (start of 1-hour meeting)

def add_busy_constraints(day_num, busy_intervals):
    for b_start, b_end in busy_intervals:
        constraint = Implies(day == day_num, Or(start >= b_end, start + 60 <= b_start))
        opt.add(constraint)

# Add constraints for each day's busy intervals
add_busy_constraints(0, busy_mon)
add_busy_constraints(1, busy_tue)
add_busy_constraints(2, busy_wed)

# Minimize the start time
opt.minimize(start)

if opt.check() == sat:
    model = opt.model()
    day_val = model[day].as_long()
    start_val = model[start].as_long()
    end_val = start_val + 60

    days = ['Monday', 'Tuesday', 'Wednesday']
    day_name = days[day_val]

    # Convert start and end times to HH:MM format
    start_hours = start_val // 60
    start_minutes = start_val % 60
    start_time = f"{start_hours:02d}:{start_minutes:02d}"

    end_hours = end_val // 60
    end_minutes = end_val % 60
    end_time = f"{end_hours:02d}:{end_minutes:02d}"

    print("SOLUTION:")
    print(f"Day: {day_name}")
    print(f"Start Time: {start_time}")
    print(f"End Time: {end_time}")
else:
    print("No solution found.")