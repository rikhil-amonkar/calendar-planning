from z3 import *

# Initialize the Z3 solver
solver = Solver()

# Define the time variables
depart_ggp = Real('depart_ggp')      # Time you leave Sunset District to head to Golden Gate Park
arrive_ggp = Real('arrive_ggp')      # Time you arrive at Golden Gate Park
depart_joshua = Real('depart_joshua') # Time you leave Golden Gate Park after meeting Joshua

# Constants
travel_time_sunset_to_ggp = 11      # minutes from Sunset District to Golden Gate Park
travel_time_ggp_to_sunset = 10       # minutes from Golden Gate Park to Sunset District
meeting_duration = 15                 # minimum meeting duration (in minutes)
joshua_start = 20.75                  # 8:45 PM in hours
joshua_end = 21.75                    # 9:45 PM in hours
arrival_time_sunset = 9.0             # 9:00 AM in hours

# Constraints
solver.add(arrive_ggp == depart_ggp + travel_time_sunset_to_ggp)  # Arrival time at Golden Gate Park
solver.add(depart_ggp >= arrival_time_sunset)  # Must leave after arriving at Sunset District
solver.add(depart_ggp <= joshua_end - (meeting_duration / 60))  # Must leave in time to meet for 15 minutes
solver.add(arrive_ggp >= joshua_start)  # Must arrive at or after Joshua starts being available
solver.add(depart_joshua >= arrive_ggp + (meeting_duration / 60))  # Must leave after meeting for 15 minutes

# Maximize the meeting time with Joshua (ideally want to meet him for at least 15 minutes)
meet_time = min(depart_joshua - arrive_ggp, meeting_duration / 60)

# We want to maximize the meeting time
solver.maximize(meet_time)

# Check if the solution is satisfiable and output the result
if solver.check() == sat:
    model = solver.model()
    depart_ggp_val = model[depart_ggp].as_decimal(2)
    arrive_ggp_val = model[arrive_ggp].as_decimal(2)
    depart_joshua_val = model[depart_joshua].as_decimal(2)

    print(f"Depart from Sunset District to Golden Gate Park at: {depart_ggp_val} hours")
    print(f"Arrive at Golden Gate Park at: {arrive_ggp_val} hours")
    print(f"Depart from Golden Gate Park after meeting Joshua at: {depart_joshua_val} hours")
else:
    print("No valid schedule found.")