from z3 import Solver, Int, Or, And, sat

s = Solver()
day = Int('day')
start = Int('start')

# Day can be 0 (Mon), 1 (Tue), 2 (Wed)
s.add(Or(day == 0, day == 1, day == 2))

# Convert all times to minutes since 9:00
# Monday constraints with John's preference (start <= 300)
monday_constraints = [
    day == 0,
    start >= 0,
    start <= 300,
    # Jennifer's Monday busy slots: 0-120, 150-240, 270-330, 360-480
    Or(start + 30 <= 0, start >= 120),   # 9:00-11:00
    Or(start + 30 <= 150, start >= 240), # 11:30-13:00
    Or(start + 30 <= 270, start >= 330), # 13:30-14:30
    Or(start + 30 <= 360, start >= 480)  # 15:00-17:00
]

# Tuesday constraints
tuesday_constraints = [
    day == 1,
    start >= 0,
    start <= 450,
    # Jennifer's Tuesday busy slots: 0-150, 180-480
    Or(start + 30 <= 0, start >= 150),  # 9:00-11:30
    Or(start + 30 <= 180, start >= 480) # 12:00-17:00
]

# Wednesday constraints
wednesday_constraints = [
    day == 2,
    start >= 0,
    start <= 450,
    # Jennifer's Wednesday busy slots: 0-150, 180-210, 240-300, 330-420, 450-480
    Or(start + 30 <= 0, start >= 150),  # 9:00-11:30
    Or(start + 30 <= 180, start >= 210), # 12:00-12:30
    Or(start + 30 <= 240, start >= 300), # 13:00-14:00
    Or(start + 30 <= 330, start >= 420), # 14:30-16:00
    Or(start + 30 <= 450, start >= 480)  # 16:30-17:00
]

s.add(Or(
    And(*monday_constraints),
    And(*tuesday_constraints),
    And(*wednesday_constraints)
))

# Minimize total time considering day order and start time
total_time = day * 480 + start
s.minimize(total_time)

if s.check() == sat:
    m = s.model()
    d = m[day].as_long()
    st = m[start].as_long()
    days = ['Monday', 'Tuesday', 'Wednesday'][d]
    hours = st // 60 + 9
    minutes = st % 60
    print(f"Meeting starts on {days} at {hours:02d}:{minutes:02d}")
else:
    print("No suitable time found.")