from z3 import *

# Initialize the Z3 solver
solver = Solver()

# Define the time variables
depart_north_beach = Real('depart_north_beach')  # Time you leave Golden Gate Park to head to North Beach
arrive_north_beach = Real('arrive_north_beach')  # Time you arrive at North Beach
depart_ronald = Real('depart_ronald')              # Time you leave North Beach after meeting Ronald

# Constants
travel_time_ggp_to_nb = 24  # minutes from Golden Gate Park to North Beach
travel_time_nb_to_ggp = 22   # minutes from North Beach to Golden Gate Park
meeting_duration = 30         # minimum meeting duration (in minutes)
ronald_start = 9.5           # 9:30 AM in hours
ronald_end = 18.5            # 6:30 PM in hours
arrival_time_ggp = 9.0       # 9:00 AM in hours

# Constraints
solver.add(arrive_north_beach == depart_north_beach + travel_time_ggp_to_nb)  # Arrival time at North Beach
solver.add(depart_north_beach >= arrival_time_ggp)  # Must leave after arriving at Golden Gate Park
solver.add(depart_north_beach <= ronald_end - (meeting_duration / 60))  # Must leave in time to meet for 30 minutes
solver.add(arrive_north_beach >= ronald_start)  # Must arrive at or after Ronald starts being available
solver.add(depart_ronald >= arrive_north_beach + (meeting_duration / 60))  # Must leave after meeting for 30 minutes

# Maximize the meeting time with Ronald (ideally want to meet him for at least 30 minutes)
meet_time = min(depart_ronald - arrive_north_beach, meeting_duration / 60)

# We want to maximize the meeting time
solver.maximize(meet_time)

# Check if the solution is satisfiable and output the result
if solver.check() == sat:
    model = solver.model()
    depart_north_beach_val = model[depart_north_beach].as_decimal(2)
    arrive_north_beach_val = model[arrive_north_beach].as_decimal(2)
    depart_ronald_val = model[depart_ronald].as_decimal(2)

    print(f"Depart from Golden Gate Park to North Beach at: {depart_north_beach_val} hours")
    print(f"Arrive at North Beach at: {arrive_north_beach_val} hours")
    print(f"Depart from North Beach after meeting Ronald at: {depart_ronald_val} hours")
else:
    print("No valid schedule found.")