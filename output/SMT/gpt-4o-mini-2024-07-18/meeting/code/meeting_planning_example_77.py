from z3 import *

# Initialize the Z3 solver
solver = Solver()

# Define the time variables
depart_ggp = Real('depart_ggp')      # Time you leave Richmond District to head to Golden Gate Park
arrive_ggp = Real('arrive_ggp')      # Time you arrive at Golden Gate Park
depart_robert = Real('depart_robert') # Time you leave Golden Gate Park after meeting Robert

# Constants
travel_time_richmond_to_ggp = 9     # minutes from Richmond District to Golden Gate Park
travel_time_ggp_to_richmond = 7      # minutes from Golden Gate Park to Richmond District
meeting_duration = 30                 # minimum meeting duration (in minutes)
robert_start = 8 + 15 / 60           # 8:15 AM in hours
robert_end = 20.5                     # 8:30 PM in hours
arrival_time_richmond = 9.0           # 9:00 AM in hours

# Constraints
solver.add(arrive_ggp == depart_ggp + travel_time_richmond_to_ggp)  # Arrival time at Golden Gate Park
solver.add(depart_ggp >= arrival_time_richmond)  # Must leave after arriving at Richmond District
solver.add(depart_ggp <= robert_end - (meeting_duration / 60))  # Must leave in time to meet for 30 minutes
solver.add(arrive_ggp >= robert_start)  # Must arrive at or after Robert starts being available
solver.add(depart_robert >= arrive_ggp + (meeting_duration / 60))  # Must leave after meeting for 30 minutes

# Maximize the meeting time with Robert (ideally want to meet him for at least 30 minutes)
meet_time = min(depart_robert - arrive_ggp, meeting_duration / 60)

# We want to maximize the meeting time
solver.maximize(meet_time)

# Check if the solution is satisfiable and output the result
if solver.check() == sat:
    model = solver.model()
    depart_ggp_val = model[depart_ggp].as_decimal(2)
    arrive_ggp_val = model[arrive_ggp].as_decimal(2)
    depart_robert_val = model[depart_robert].as_decimal(2)

    print(f"Depart from Richmond District to Golden Gate Park at: {depart_ggp_val} hours")
    print(f"Arrive at Golden Gate Park at: {arrive_ggp_val} hours")
    print(f"Depart from Golden Gate Park after meeting Robert at: {depart_robert_val} hours")
else:
    print("No valid schedule found.")