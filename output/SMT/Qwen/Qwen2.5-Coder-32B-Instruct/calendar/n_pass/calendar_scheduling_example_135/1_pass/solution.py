from z3 import *

# Define the variables for the meeting time
day = Int('day')
start_time = Int('start_time')
end_time = Int('end_time')

# Define the constraints
meeting_duration = 30  # Meeting duration in minutes

# Constraints for the meeting time
constraints = [
    day == 1,  # Monday is represented as 1
    start_time >= 9 * 60,  # Start time must be after or at 9:00 AM
    end_time <= 17 * 60,   # End time must be before or at 5:00 PM
    end_time - start_time == meeting_duration  # Meeting duration is 30 minutes
]

# Eric's availability: No meetings the whole day, so no additional constraints

# Ashley's busy times: 10:00-10:30, 11:00-12:00, 12:30-13:00, 15:00-16:00
ashley_busy_times = [
    (10 * 60, 10 * 60 + 30),
    (11 * 60, 12 * 60),
    (12 * 60 + 30, 13 * 60),
    (15 * 60, 16 * 60)
]
for start, end in ashley_busy_times:
    constraints.append(Or(start_time >= end, end_time <= start))

# Ronald's busy times: 9:00-9:30, 10:00-11:30, 12:30-14:00, 14:30-17:00
ronald_busy_times = [
    (9 * 60, 9 * 60 + 30),
    (10 * 60, 11 * 60 + 30),
    (12 * 60 + 30, 14 * 60),
    (14 * 60 + 30, 17 * 60)
]
for start, end in ronald_busy_times:
    constraints.append(Or(start_time >= end, end_time <= start))

# Larry's blocked times: 9:00-12:00, 13:00-17:00
larry_blocked_times = [
    (9 * 60, 12 * 60),
    (13 * 60, 17 * 60)
]
for start, end in larry_blocked_times:
    constraints.append(Or(start_time >= end, end_time <= start))

# Create the solver and add the constraints
solver = Solver()
solver.add(constraints)

# Check if there is a solution
if solver.check() == sat:
    model = solver.model()
    start_hour = model[start_time].as_long() // 60
    start_minute = model[start_time].as_long() % 60
    end_hour = model[end_time].as_long() // 60
    end_minute = model[end_time].as_long() % 60
    
    print("SOLUTION:")
    print(f"Day: Monday")
    print(f"Start Time: {start_hour:02}:{start_minute:02}")
    print(f"End Time: {end_hour:02}:{end_minute:02}")
else:
    print("No solution found.")