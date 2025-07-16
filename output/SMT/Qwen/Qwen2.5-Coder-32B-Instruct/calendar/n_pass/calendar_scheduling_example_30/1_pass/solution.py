from z3 import *

# Define the variables for the meeting time
day = Int('day')  # We only need to consider Monday, so this will be fixed to 1
start_hour = Int('start_hour')
start_minute = Int('start_minute')
end_hour = Int('end_hour')
end_minute = Int('end_minute')

# Define the duration of the meeting
meeting_duration = 30  # 30 minutes

# Constraints for the meeting time
constraints = [
    day == 1,  # We are only considering Monday
    start_hour >= 9, start_hour < 17,  # Meeting must be within work hours
    Or(start_minute == 0, start_minute == 30),  # Meeting can only start on the hour or half-hour
    end_hour == start_hour + (start_minute + meeting_duration) // 60,
    end_minute == (start_minute + meeting_duration) % 60,
    end_hour < 17,  # Meeting must end before 17:00
]

# Constraints for Jeffrey's availability
jeffrey_busy_times = [(9, 30, 10, 0), (10, 30, 11, 0)]
for start_h, start_m, end_h, end_m in jeffrey_busy_times:
    constraints.append(Or(end_hour < start_h, Or(end_hour == start_h, end_minute <= start_m),
                         start_hour > end_h, Or(start_hour == end_h, start_minute >= end_m)))

# Constraints for Virginia's availability
virginia_busy_times = [(9, 0, 9, 30), (10, 0, 10, 30), (14, 30, 15, 0), (16, 0, 16, 30)]
for start_h, start_m, end_h, end_m in virginia_busy_times:
    constraints.append(Or(end_hour < start_h, Or(end_hour == start_h, end_minute <= start_m),
                         start_hour > end_h, Or(start_hour == end_h, start_minute >= end_m)))

# Constraints for Melissa's availability
melissa_busy_times = [(9, 0, 11, 30), (12, 0, 12, 30), (13, 0, 15, 0), (16, 0, 17, 0)]
for start_h, start_m, end_h, end_m in melissa_busy_times:
    constraints.append(Or(end_hour < start_h, Or(end_hour == start_h, end_minute <= start_m),
                         start_hour > end_h, Or(start_hour == end_h, start_minute >= end_m)))

# Melissa's preference: do not meet after 14:00
constraints.append(Or(end_hour < 14, Or(end_hour == 14, end_minute == 0)))

# Create a solver instance and add constraints
solver = Solver()
solver.add(constraints)

# Check if there is a solution
if solver.check() == sat:
    model = solver.model()
    start_time = f"{model[start_hour].as_long()}:{model[start_minute].as_long():02d}"
    end_time = f"{model[end_hour].as_long()}:{model[end_minute].as_long():02d}"
    print(f"SOLUTION:\nDay: Monday\nStart Time: {start_time}\nEnd Time: {end_time}")
else:
    print("No solution found")