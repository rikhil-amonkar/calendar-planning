from z3 import *

# Create the Z3 solver
solver = Solver()

# Define variables:
# day: 0 for Monday, 1 for Tuesday
day = Int('day')
start = Int('start')  # Meeting start time in minutes after midnight
end = start + 60      # Meeting end time (duration 60 minutes)

# Working hours: 9:00 to 17:00 (i.e., 540 to 1020 minutes)
solver.add(Or(day == 0, day == 1))
solver.add(start >= 540)
solver.add(start <= 1020 - 60)  # so that end = start+60 <= 1020

# Function to add a non-overlap constraint:
# For a given busy interval (busy_start, busy_end),
# the meeting must either end on or before busy_start,
# or start on or after busy_end.
def avoid_conflict(busy_start, busy_end):
    return Or(end <= busy_start, start >= busy_end)

# Patricia's meetings:
# Monday (day==0) busy intervals (in minutes):
patricia_mon_busy = [
    (600, 630),   # 10:00 to 10:30
    (690, 720),   # 11:30 to 12:00
    (780, 810),   # 13:00 to 13:30
    (870, 930),   # 14:30 to 15:30
    (960, 990)    # 16:00 to 16:30
]
for s_busy, e_busy in patricia_mon_busy:
    solver.add(Implies(day == 0, avoid_conflict(s_busy, e_busy)))

# Tuesday (day==1) busy intervals for Patricia:
patricia_tue_busy = [
    (600, 630),   # 10:00 to 10:30
    (660, 720),   # 11:00 to 12:00
    (840, 960),   # 14:00 to 16:00
    (990, 1020)   # 16:30 to 17:00
]
for s_busy, e_busy in patricia_tue_busy:
    solver.add(Implies(day == 1, avoid_conflict(s_busy, e_busy)))

# Jesse's meetings:
# Monday (day==0) busy interval: all day busy (9:00 to 17:00)
solver.add(Implies(day == 0, avoid_conflict(540, 1020)))

# Tuesday (day==1) busy intervals for Jesse:
jesse_tue_busy = [
    (660, 690),   # 11:00 to 11:30
    (720, 750),   # 12:00 to 12:30
    (780, 840),   # 13:00 to 14:00
    (870, 900),   # 14:30 to 15:00
    (930, 1020)   # 15:30 to 17:00
]
for s_busy, e_busy in jesse_tue_busy:
    solver.add(Implies(day == 1, avoid_conflict(s_busy, e_busy)))

# Solve the constraints
if solver.check() == sat:
    model = solver.model()
    day_val = model[day].as_long()
    start_val = model[start].as_long()
    end_val = start_val + 60

    # Map day value to string
    day_str = "Monday" if day_val == 0 else "Tuesday"

    # Convert minutes to HH:MM (24-hour format)
    def minutes_to_time(m):
        h = m // 60
        m_remainder = m % 60
        return f"{h:02d}:{m_remainder:02d}"

    # Output the solution in the required format
    print("SOLUTION:")
    print("Day:", day_str)
    print("Start Time:", minutes_to_time(start_val))
    print("End Time:", minutes_to_time(end_val))
else:
    print("No solution found.")