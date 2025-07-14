from z3 import *

# Define the variables
day = Int('day')  # 0 = Monday, 1 = Tuesday, 2 = Wednesday, 3 = Thursday
start_time = Int('start_time')  # in minutes from 9:00

# Define the constraints for the days
days = [0, 1, 2, 3]  # Monday, Tuesday, Wednesday, Thursday

# Define the constraints for Megan's availability
megan_busy = [
    (0, 13*60, 13*60 + 30),  # Monday 13:00 to 13:30
    (0, 14*60, 15*60 + 30),  # Monday 14:00 to 15:30
    (1, 9*60, 9*60 + 30),   # Tuesday 9:00 to 9:30
    (1, 12*60, 12*60 + 30),  # Tuesday 12:00 to 12:30
    (1, 16*60, 17*60),      # Tuesday 16:00 to 17:00
    (2, 9*60 + 30, 10*60),  # Wednesday 9:30 to 10:00
    (2, 10*60 + 30, 11*60 + 30),  # Wednesday 10:30 to 11:30
    (2, 12*60 + 30, 14*60),  # Wednesday 12:30 to 14:00
    (2, 16*60, 16*60 + 30),  # Wednesday 16:00 to 16:30
    (3, 13*60 + 30, 14*60 + 30),  # Thursday 13:30 to 14:30
    (3, 15*60, 15*60 + 30)   # Thursday 15:00 to 15:30
]

# Define the constraints for Daniel's availability
daniel_busy = [
    (0, 10*60, 11*60 + 30),  # Monday 10:00 to 11:30
    (0, 12*60 + 30, 15*60),  # Monday 12:30 to 15:00
    (1, 9*60, 10*60),       # Tuesday 9:00 to 10:00
    (1, 10*60 + 30, 17*60),  # Tuesday 10:30 to 17:00
    (2, 9*60, 10*60),       # Wednesday 9:00 to 10:00
    (2, 10*60 + 30, 11*60 + 30),  # Wednesday 10:30 to 11:30
    (2, 12*60, 17*60),      # Wednesday 12:00 to 17:00
    (3, 9*60, 12*60),       # Thursday 9:00 to 12:00
    (3, 12*60 + 30, 14*60 + 30),  # Thursday 12:30 to 14:30
    (3, 15*60, 15*60 + 30),  # Thursday 15:00 to 15:30
    (3, 16*60, 17*60)       # Thursday 16:00 to 17:00
]

# Create a solver instance
s = Solver()

# Add constraints for the day
s.add(day >= 0)
s.add(day <= 3)

# Add constraints for the start time
s.add(start_time >= 9*60)
s.add(start_time <= 17*60 - 60)  # Meeting duration is 1 hour

# Add constraints for Megan's availability
for d, start, end in megan_busy:
    s.add(Or(day != d, Or(start_time + 60 <= start, start_time >= end)))

# Add constraints for Daniel's availability
for d, start, end in daniel_busy:
    s.add(Or(day != d, Or(start_time + 60 <= start, start_time >= end)))

# Check if the constraints are satisfiable
if s.check() == sat:
    m = s.model()
    day_value = m[day].as_long()
    start_time_value = m[start_time].as_long()
    end_time_value = start_time_value + 60
    
    day_names = ["Monday", "Tuesday", "Wednesday", "Thursday"]
    start_time_str = f"{start_time_value // 60:02}:{start_time_value % 60:02}"
    end_time_str = f"{end_time_value // 60:02}:{end_time_value % 60:02}"
    
    print(f"SOLUTION:\nDay: {day_names[day_value]}\nStart Time: {start_time_str}\nEnd Time: {end_time_str}")
else:
    print("No solution found")