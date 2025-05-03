from z3 import *

# Initialize the Z3 solver
solver = Solver()

# Define the time variables
depart_gg_park = Real('depart_gg_park')  # Time we leave The Castro to head to Golden Gate Park
arrive_gg_park = Real('arrive_gg_park')  # Time we arrive at Golden Gate Park
depart_jeffrey = Real('depart_jeffrey')   # Time we leave Golden Gate Park after meeting with Jeffrey

# Constants
travel_time_castro_to_gg_park = 11  # minutes
travel_time_gg_park_to_castro = 13   # minutes
meeting_duration = 105                # minutes
jeffrey_start = 7.0                  # 7:00 AM in hours
jeffrey_end = 17.5                   # 5:30 PM in hours
arrival_time_castro = 9.0             # 9:00 AM in hours

# Constraints
solver.add(arrive_gg_park == depart_gg_park + travel_time_castro_to_gg_park)
solver.add(depart_gg_park >= arrival_time_castro)  # Must leave after arriving at The Castro
solver.add(depart_gg_park <= jeffrey_end - meeting_duration)  # Must leave in time to meet for 105 minutes
solver.add(arrive_gg_park >= jeffrey_start)  # Must arrive at or after Jeffrey starts being available
solver.add(depart_jeffrey >= arrive_gg_park + meeting_duration)  # Must leave after meeting for 105 minutes

# Maximize the meeting time with Jeffrey (ideally want to meet him for 105 minutes)
meet_time = min(depart_jeffrey - arrive_gg_park, meeting_duration)

# We want to maximize the meeting time
solver.maximize(meet_time)

# Check if the solution is satisfiable and output the result
if solver.check() == sat:
    model = solver.model()
    depart_gg_park_val = model[depart_gg_park].as_decimal(2)
    arrive_gg_park_val = model[arrive_gg_park].as_decimal(2)
    depart_jeffrey_val = model[depart_jeffrey].as_decimal(2)

    print(f"Depart from The Castro to Golden Gate Park at: {depart_gg_park_val} hours")
    print(f"Arrive at Golden Gate Park at: {arrive_gg_park_val} hours")
    print(f"Depart from Golden Gate Park after meeting Jeffrey at: {depart_jeffrey_val} hours")
else:
    print("No valid schedule found.")