from z3 import *

# Initialize the Z3 solver
solver = Solver()

# Define the time variables
depart_gg_park = Real('depart_gg_park')  # Time at which we leave Russian Hill to head to Golden Gate Park
arrive_gg_park = Real('arrive_gg_park')  # Time at which we arrive at Golden Gate Park
depart_john = Real('depart_john')  # Time we leave Golden Gate Park after meeting with John

# Constants
travel_time_russian_hill_to_gg_park = 21  # minutes
meeting_duration = 90  # minutes
john_start = 13.0      # 1:00 PM in hours
john_end = 18.25       # 6:15 PM in hours
arrival_time_russian_hill = 9.0  # 9:00 AM in hours

# Constraints
solver.add(arrive_gg_park == depart_gg_park + travel_time_russian_hill_to_gg_park)
solver.add(depart_gg_park >= arrival_time_russian_hill)  # Must leave after arriving at Russian Hill
solver.add(depart_gg_park <= john_end - meeting_duration)  # Must leave in time to meet John for 90 minutes
solver.add(arrive_gg_park >= john_start)  # Must arrive at or after John starts being available
solver.add(depart_john >= arrive_gg_park + meeting_duration)  # Must leave after meeting for 90 minutes

# Maximize the meeting time with John (ideally want to meet him for 90 minutes)
meet_time = min(depart_john - arrive_gg_park, meeting_duration)

# We want to maximize the meeting time
solver.maximize(meet_time)

# Check if the solution is satisfiable and output the result
if solver.check() == sat:
    model = solver.model()
    depart_gg_park_val = model[depart_gg_park].as_decimal(2)
    arrive_gg_park_val = model[arrive_gg_park].as_decimal(2)
    depart_john_val = model[depart_john].as_decimal(2)

    print(f"Depart from Russian Hill to Golden Gate Park at: {depart_gg_park_val} hours")
    print(f"Arrive at Golden Gate Park at: {arrive_gg_park_val} hours")
    print(f"Depart from Golden Gate Park after meeting John at: {depart_john_val} hours")
else:
    print("No valid schedule found.")