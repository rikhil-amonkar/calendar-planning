from z3 import *

def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

solver = Solver()
start_time = Int('start_time')

# Define work hours constraints (9:00 to 17:00, meeting is 1 hour)
solver.add(start_time >= 9 * 60)          # 9:00 AM
solver.add(start_time <= 16 * 60)          # 16:00 PM (to end by 17:00)

# Busy intervals converted to minutes since midnight
busy_intervals = [
    # Stephanie
    (10 * 60, 10 * 60 + 30),  # 10:00-10:30
    (16 * 60, 16 * 60 + 30),  # 16:00-16:30
    # Cheryl
    (10 * 60, 10 * 60 + 30),  # 10:00-10:30
    (11 * 60 + 30, 12 * 60),  # 11:30-12:00
    (13 * 60 + 30, 14 * 60),  # 13:30-14:00
    (16 * 60 + 30, 17 * 60),  # 16:30-17:00
    # Bradley
    (9 * 60 + 30, 10 * 60),   # 9:30-10:00
    (10 * 60 + 30, 11 * 60 + 30),  # 10:30-11:30
    (13 * 60 + 30, 14 * 60),  # 13:30-14:00
    (14 * 60 + 30, 15 * 60),  # 14:30-15:00
    (15 * 60 + 30, 17 * 60),  # 15:30-17:00
    # Steven
    (9 * 60, 12 * 60),        # 9:00-12:00
    (13 * 60, 13 * 60 + 30),  # 13:00-13:30
    (14 * 60 + 30, 17 * 60),  # 14:30-17:00
]

# Add constraints for each busy interval
for s, e in busy_intervals:
    solver.add(Or(start_time + 60 <= s, e <= start_time))

if solver.check() == sat:
    model = solver.model()
    start = model[start_time].as_long()
    end = start + 60
    print("SOLUTION:")
    print(f"Day: Monday")
    print(f"Start Time: {minutes_to_time(start)}")
    print(f"End Time: {minutes_to_time(end)}")