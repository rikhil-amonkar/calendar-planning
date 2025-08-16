from z3 import *

# Create the Z3 solver
solver = Solver()

# Define decision variables:
# "day" is an integer: 0=Monday, 1=Tuesday, 2=Wednesday, 3=Thursday, 4=Friday
day = Int('day')

# "m" is the meeting start time in minutes after 9:00.
# For example, m = 0 represents 09:00, and because the meeting is 30 minutes long,
# we require m + 30 <= 480 (17:00 is 480 minutes after 9:00).
m = Int('m')

# The meeting must start during work hours.
solver.add(m >= 0, m + 30 <= 480)

# The day must be one of Monday-Friday.
solver.add(day >= 0, day <= 4)

# Preferences on days:
# Daniel prefers not to meet on Wednesday (2) or Thursday (3).
solver.add(day != 2, day != 3)
# Bradley does not want to meet on Monday (0) or Friday (4).
solver.add(day != 0, day != 4)
# Additionally, Bradley does not want a meeting on Tuesday before 12:00.
# Since work hours start at 09:00, Tuesday 12:00 corresponds to 180 minutes after 9:00.
solver.add(If(day == 1, m >= 180, True))

# Busy intervals are given per day.
# Each tuple is of the form: (day, start, end)
# The start and end of each busy interval are represented as minutes after 9:00.
# For example, 9:30 is 30 and 10:30 is 90.

# Daniel's busy intervals.
daniel_busy = [
    (0, 30, 90),    # Monday 9:30-10:30
    (0, 180, 210),  # Monday 12:00-12:30
    (0, 240, 300),  # Monday 13:00-14:00
    (0, 330, 360),  # Monday 14:30-15:00
    (0, 390, 420),  # Monday 15:30-16:00
    (1, 120, 180),  # Tuesday 11:00-12:00
    (1, 240, 270),  # Tuesday 13:00-13:30
    (1, 390, 420),  # Tuesday 15:30-16:00
    (1, 450, 480),  # Tuesday 16:30-17:00
    (2, 0, 60),     # Wednesday 9:00-10:00
    (2, 300, 330),  # Wednesday 14:00-14:30
    (3, 90, 120),   # Thursday 10:30-11:00
    (3, 180, 240),  # Thursday 12:00-13:00
    (3, 330, 360),  # Thursday 14:30-15:00
    (3, 390, 420),  # Thursday 15:30-16:00
    (4, 0, 30),     # Friday 9:00-9:30
    (4, 150, 180),  # Friday 11:30-12:00
    (4, 240, 270),  # Friday 13:00-13:30
    (4, 450, 480)   # Friday 16:30-17:00
]

# Bradley's busy intervals.
bradley_busy = [
    (0, 30, 120),   # Monday 9:30-11:00
    (0, 150, 180),  # Monday 11:30-12:00
    (0, 210, 240),  # Monday 12:30-13:00
    (0, 300, 360),  # Monday 14:00-15:00
    (1, 90, 120),   # Tuesday 10:30-11:00
    (1, 180, 240),  # Tuesday 12:00-13:00
    (1, 270, 300),  # Tuesday 13:30-14:00
    (1, 390, 450),  # Tuesday 15:30-16:30
    (2, 0, 60),     # Wednesday 9:00-10:00
    (2, 120, 240),  # Wednesday 11:00-13:00
    (2, 270, 300),  # Wednesday 13:30-14:00
    (2, 330, 480),  # Wednesday 14:30-17:00
    (3, 0, 210),    # Thursday 9:00-12:30
    (3, 270, 300),  # Thursday 13:30-14:00
    (3, 330, 360),  # Thursday 14:30-15:00
    (3, 390, 450),  # Thursday 15:30-16:30
    (4, 0, 30),     # Friday 9:00-9:30
    (4, 60, 210),   # Friday 10:00-12:30
    (4, 240, 270),  # Friday 13:00-13:30
    (4, 300, 330),  # Friday 14:00-14:30
    (4, 390, 450)   # Friday 15:30-16:30
]

# For each busy interval, if the meeting is scheduled on that day,
# ensure that the meeting (interval [m, m+30]) does not overlap with the busy interval.
for (d, busy_start, busy_end) in daniel_busy:
    solver.add(Implies(day == d, Or(m + 30 <= busy_start, m >= busy_end)))

for (d, busy_start, busy_end) in bradley_busy:
    solver.add(Implies(day == d, Or(m + 30 <= busy_start, m >= busy_end)))

# Check if the constraints are satisfiable.
if solver.check() == sat:
    model = solver.model()
    day_val = model[day].as_long()
    m_val = model[m].as_long()
    
    # Map the day number to weekday name.
    days = {0: "Monday", 1: "Tuesday", 2: "Wednesday", 3: "Thursday", 4: "Friday"}
    day_str = days[day_val]
    
    # Convert meeting start time to HH:MM.
    # m_val is the minutes offset from 9:00. So add 9 hours.
    start_total = 9 * 60 + m_val
    start_hour = start_total // 60
    start_min = start_total % 60
    
    # The meeting lasts 30 minutes.
    end_total = start_total + 30
    end_hour = end_total // 60
    end_min = end_total % 60
    
    # Format times as HH:MM (24-hour format)
    start_time_str = f"{start_hour:02d}:{start_min:02d}"
    end_time_str = f"{end_hour:02d}:{end_min:02d}"
    
    # Output the solution in the required format.
    print("SOLUTION:")
    print(f"Day: {day_str}")
    print(f"Start Time: {start_time_str}")
    print(f"End Time: {end_time_str}")
else:
    print("No solution found.")