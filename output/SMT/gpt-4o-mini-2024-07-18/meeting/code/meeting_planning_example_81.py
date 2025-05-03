from z3 import *

# Initialize the Z3 solver
solver = Solver()

# Define the time variables
depart_alamo = Real('depart_alamo')  # Time you leave Richmond District to head to Alamo Square
arrive_alamo = Real('arrive_alamo')  # Time you arrive at Alamo Square
depart_betty = Real('depart_betty')   # Time you leave Alamo Square after meeting Betty

# Constants
travel_time_richmond_to_alamo = 13   # minutes from Richmond District to Alamo Square
travel_time_alamo_to_richmond = 12    # minutes from Alamo Square to Richmond District
meeting_duration = 75                  # minimum meeting duration (in minutes)
betty_start = 12.5                    # 12:30 PM in hours
betty_end = 19.25                     # 7:15 PM in hours
arrival_time_richmond = 9.0            # 9:00 AM in hours

# Constraints
solver.add(arrive_alamo == depart_alamo + travel_time_richmond_to_alamo)  # Arrival time at Alamo Square
solver.add(depart_alamo >= arrival_time_richmond)  # Must leave after arriving at Richmond District
solver.add(depart_alamo <= betty_end - (meeting_duration / 60))  # Must leave in time to meet for 75 minutes
solver.add(arrive_alamo >= betty_start)  # Must arrive at or after Betty starts being available
solver.add(depart_betty >= arrive_alamo + (meeting_duration / 60))  # Must leave after meeting for 75 minutes

# Maximize the meeting time with Betty (ideally want to meet her for at least 75 minutes)
meet_time = min(depart_betty - arrive_alamo, meeting_duration / 60)

# We want to maximize the meeting time
solver.maximize(meet_time)

# Check if the solution is satisfiable and output the result
if solver.check() == sat:
    model = solver.model()
    depart_alamo_val = model[depart_alamo].as_decimal(2)
    arrive_alamo_val = model[arrive_alamo].as_decimal(2)
    depart_betty_val = model[depart_betty].as_decimal(2)

    print(f"Depart from Richmond District to Alamo Square at: {depart_alamo_val} hours")
    print(f"Arrive at Alamo Square at: {arrive_alamo_val} hours")
    print(f"Depart from Alamo Square after meeting Betty at: {depart_betty_val} hours")
else:
    print("No valid schedule found.")