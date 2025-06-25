from z3 import *

# Define the variables
start_time = Int('start_time')  # Start time in minutes
end_time = Int('end_time')  # End time in minutes
distance_to_ggp = 11  # Distance from Sunset District to Golden Gate Park in minutes
distance_from_ggp_to_sd = 10  # Distance from Golden Gate Park to Sunset District in minutes
joshua_start_time = 8 * 60 + 45  # Joshua's start time in minutes
joshua_end_time = 9 * 60 + 45  # Joshua's end time in minutes
min_meeting_time = 15  # Minimum meeting time in minutes

# Define the constraints
s = Optimize()
s.add(start_time >= 0)  # Start time should be non-negative
s.add(end_time >= start_time)  # End time should be greater than or equal to start time
s.add(end_time - start_time >= min_meeting_time)  # Meeting time should be greater than or equal to minimum meeting time
s.add(start_time + distance_to_ggp <= joshua_start_time)  # Arrival time at Golden Gate Park should be before Joshua's start time
s.add(joshua_end_time <= start_time + distance_from_ggp_to_sd)  # Departure time from Golden Gate Park should be after Joshua's end time

# Define the objective function
s.minimize(end_time - start_time)  # Minimize the end time minus start time, which is equivalent to minimizing the duration of the trip

# Solve the optimization problem
result = s.check()
if result == sat:
    model = s.model()
    print(f"Start time: {model[start_time].as_long()} minutes")
    print(f"End time: {model[end_time].as_long()} minutes")
else:
    print("No solution found")