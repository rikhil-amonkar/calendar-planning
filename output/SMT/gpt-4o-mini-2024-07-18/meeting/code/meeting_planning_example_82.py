from z3 import *

# Initialize the Z3 solver
solver = Solver()

# Define the time variables
depart_alamo = Real('depart_alamo')  # Time you leave Golden Gate Park to head to Alamo Square
arrive_alamo = Real('arrive_alamo')  # Time you arrive at Alamo Square
depart_ashley = Real('depart_ashley') # Time you leave Alamo Square after meeting Ashley

# Constants
travel_time_ggp_to_alamo = 10       # minutes from Golden Gate Park to Alamo Square
travel_time_alamo_to_ggp = 9         # minutes from Alamo Square to Golden Gate Park
meeting_duration = 75                 # minimum meeting duration (in minutes)
ashley_start = 17.75                 # 5:45 PM in hours
ashley_end = 21.5                    # 9:30 PM in hours
arrival_time_ggp = 9.0               # 9:00 AM in hours

# Constraints
solver.add(arrive_alamo == depart_alamo + travel_time_ggp_to_alamo)  # Arrival time at Alamo Square
solver.add(depart_alamo >= arrival_time_ggp)  # Must leave after arriving at Golden Gate Park
solver.add(depart_alamo <= ashley_end - (meeting_duration / 60))  # Must leave in time to meet for 75 minutes
solver.add(arrive_alamo >= ashley_start)  # Must arrive at or after Ashley starts being available
solver.add(depart_ashley >= arrive_alamo + (meeting_duration / 60))  # Must leave after meeting for 75 minutes

# Maximize the meeting time with Ashley (ideally want to meet her for at least 75 minutes)
meet_time = min(depart_ashley - arrive_alamo, meeting_duration / 60)

# We want to maximize the meeting time
solver.maximize(meet_time)

# Check if the solution is satisfiable and output the result
if solver.check() == sat:
    model = solver.model()
    depart_alamo_val = model[depart_alamo].as_decimal(2)
    arrive_alamo_val = model[arrive_alamo].as_decimal(2)
    depart_ashley_val = model[depart_ashley].as_decimal(2)

    print(f"Depart from Golden Gate Park to Alamo Square at: {depart_alamo_val} hours")
    print(f"Arrive at Alamo Square at: {arrive_alamo_val} hours")
    print(f"Depart from Alamo Square after meeting Ashley at: {depart_ashley_val} hours")
else:
    print("No valid schedule found.")