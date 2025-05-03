from z3 import *

# Initialize the Z3 solver
solver = Solver()

# Define the time variables
depart_sunset = Real('depart_sunset')  # Time at which we leave Alamo Square to head to Sunset District
arrive_sunset = Real('arrive_sunset')  # Time at which we arrive at Sunset District
depart_matthew = Real('depart_matthew')  # Time we leave Sunset District after meeting with Matthew

# Constants
travel_time_alamo_to_sunset = 16  # minutes
meeting_duration = 15              # minutes
matthew_start = 13.5              # 1:30 PM in hours
matthew_end = 14.5                # 2:30 PM in hours
arrival_time_alamo = 9.0          # 9:00 AM in hours

# Constraints
solver.add(arrive_sunset == depart_sunset + travel_time_alamo_to_sunset)
solver.add(depart_sunset >= arrival_time_alamo)  # Must leave after arriving at Alamo Square
solver.add(depart_sunset <= matthew_end - meeting_duration)  # Must leave in time to meet for 15 minutes
solver.add(arrive_sunset >= matthew_start)  # Must arrive at or after Matthew starts being available
solver.add(depart_matthew >= arrive_sunset + meeting_duration)  # Must leave after meeting for 15 minutes

# Maximize the meeting time with Matthew (ideally want to meet him for 15 minutes)
meet_time = min(depart_matthew - arrive_sunset, meeting_duration)

# We want to maximize the meeting time
solver.maximize(meet_time)

# Check if the solution is satisfiable and output the result
if solver.check() == sat:
    model = solver.model()
    depart_sunset_val = model[depart_sunset].as_decimal(2)
    arrive_sunset_val = model[arrive_sunset].as_decimal(2)
    depart_matthew_val = model[depart_matthew].as_decimal(2)

    print(f"Depart from Alamo Square to Sunset District at: {depart_sunset_val} hours")
    print(f"Arrive at Sunset District at: {arrive_sunset_val} hours")
    print(f"Depart from Sunset District after meeting Matthew at: {depart_matthew_val} hours")
else:
    print("No valid schedule found.")