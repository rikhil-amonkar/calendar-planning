from z3 import *

# Define the variables for the meeting time
start_hour = Int('start_hour')
start_minute = Int('start_minute')

# Define the duration of the meeting
meeting_duration = 30  # in minutes

# Constraints for the time range (9:00 to 17:00)
time_range_constraint = And(
    start_hour >= 9,
    start_hour <= 16,
    Or(start_hour < 16, start_minute + meeting_duration <= 60)
)

# Constraints for each participant
adam_busy = Not(
    And(start_hour == 14, start_minute >= 0, start_minute < 60)
)
john_busy = Not(
    Or(
        And(start_hour == 13, start_minute >= 0, start_minute < 30),
        And(start_hour == 14, start_minute >= 0, start_minute < 30),
        And(start_hour == 15, start_minute >= 30, start_minute < 60),
        And(start_hour == 16, start_minute >= 30, start_minute < 60)
    )
)
stephanie_busy = Not(
    Or(
        And(start_hour == 9, start_minute >= 30, start_minute < 60),
        And(start_hour == 10, start_minute >= 0, start_minute < 30),
        And(start_hour == 10, start_minute >= 30, start_minute < 60),
        And(start_hour == 11, start_minute >= 30, start_minute < 60),
        And(start_hour == 16, start_minute >= 0, start_minute < 30)
    )
)
anna_busy = Not(
    Or(
        And(start_hour == 9, start_minute >= 30, start_minute < 60),
        And(start_hour == 12, start_minute >= 0, start_minute < 30),
        And(start_hour == 13, start_minute >= 0, start_minute < 60),
        And(start_hour == 14, start_minute >= 0, start_minute < 30),
        And(start_hour == 15, start_minute >= 0, start_minute < 60),
        And(start_hour == 16, start_minute >= 0, start_minute < 30)
    )
)
anna_preference = Or(
    start_hour > 14,
    And(start_hour == 14, start_minute >= 30)
)

# Combine all constraints
constraints = [
    time_range_constraint,
    adam_busy,
    john_busy,
    stephanie_busy,
    anna_busy,
    anna_preference
]

# Create a solver and add the constraints
solver = Solver()
solver.add(constraints)

# Check if the constraints are satisfiable
if solver.check() == sat:
    model = solver.model()
    start_time_hour = model[start_hour].as_long()
    start_time_minute = model[start_minute].as_long()
    end_time_hour = start_time_hour + (start_time_minute + meeting_duration) // 60
    end_time_minute = (start_time_minute + meeting_duration) % 60
    
    # Format the output
    start_time = f"{start_time_hour:02}:{start_time_minute:02}"
    end_time = f"{end_time_hour:02}:{end_time_minute:02}"
    
    print("SOLUTION:")
    print(f"Day: Monday")
    print(f"Start Time: {start_time}")
    print(f"End Time: {end_time}")
else:
    print("No solution found")