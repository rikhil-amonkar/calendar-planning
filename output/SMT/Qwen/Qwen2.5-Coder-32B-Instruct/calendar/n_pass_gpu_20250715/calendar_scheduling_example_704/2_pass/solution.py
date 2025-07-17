from z3 import *

# Define the variables for the day and time
day = Int('day')  # 0 = Monday, 1 = Tuesday, 2 = Wednesday
start_time = Int('start_time')  # In minutes since 9:00

# Constraints for the day
day_constraints = And(0 <= day, day <= 2)

# Constraints for the start time
time_constraints = And(0 <= start_time, start_time + 30 <= 480)  # 480 minutes is 8 hours (from 9:00 to 17:00)

# Samuel's busy times in minutes since 9:00
samuel_busy_times = [
    (90, 120),  # Monday 10:30 - 11:00
    (180, 210),  # Monday 12:00 - 12:30
    (210, 900),  # Monday 13:00 - 15:00
    (930, 1050),  # Monday 15:30 - 16:30
    (0, 180),  # Tuesday 9:00 - 12:00
    (840, 930),  # Tuesday 14:00 - 15:30
    (990, 1080),  # Tuesday 16:30 - 17:00
    (90, 120),  # Wednesday 10:30 - 11:00
    (150, 180),  # Wednesday 11:30 - 12:00
    (210, 240),  # Wednesday 12:30 - 13:00
    (840, 870),  # Wednesday 14:00 - 14:30
    (900, 960)   # Wednesday 15:00 - 16:00
]

# Constraints to avoid Samuel's busy times
samuel_availability = And([Or(start_time + 30 <= busy_start, start_time >= busy_end) for busy_start, busy_end in samuel_busy_times])

# Preference constraints
# Larry prefers not to meet on Wednesday
larry_preference = If(day == 2, 1, 0)

# Samuel prefers not to meet on Tuesday
samuel_preference = If(day == 1, 1, 0)

# Total preference score
preference_score = larry_preference + samuel_preference

# Create the solver
solver = Optimize()

# Add all constraints to the solver
solver.add(day_constraints)
solver.add(time_constraints)
solver.add(samuel_availability)

# Minimize the preference score
solver.minimize(preference_score)

# Check if there is a solution
if solver.check() == sat:
    model = solver.model()
    day_value = model[day].as_long()
    start_time_value = model[start_time].as_long()
    end_time_value = start_time_value + 30
    
    # Convert day value to string
    days = ["Monday", "Tuesday", "Wednesday"]
    day_str = days[day_value]
    
    # Convert start and end times to HH:MM format
    start_time_str = f"{9 + start_time_value // 60:02}:{start_time_value % 60:02}"
    end_time_str = f"{9 + end_time_value // 60:02}:{end_time_value % 60:02}"
    
    print(f"SOLUTION:\nDay: {day_str}\nStart Time: {start_time_str}\nEnd Time: {end_time_str}")
else:
    print("No solution found")