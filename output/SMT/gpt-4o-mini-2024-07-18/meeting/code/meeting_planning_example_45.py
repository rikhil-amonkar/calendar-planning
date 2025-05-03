from z3 import *

# Initialize the Z3 solver
solver = Solver()

# Define the time variables
depart_alamo = Real('depart_alamo')  # Time you leave North Beach to head to Alamo Square
arrive_alamo = Real('arrive_alamo')  # Time you arrive at Alamo Square
depart_emily = Real('depart_emily')   # Time you leave Alamo Square after meeting Emily

# Constants
travel_time_nb_to_as = 16  # Travel time from North Beach to Alamo Square (in minutes)
travel_time_as_to_nb = 15   # Travel time from Alamo Square to North Beach (in minutes)
meeting_duration = 15        # Minimum meeting duration (in minutes)
emily_start = 19.5          # 7:30 PM in hours
emily_end = 21.0            # 9:00 PM in hours
arrival_time_nb = 9.0       # 9:00 AM in hours

# Constraints
solver.add(arrive_alamo == depart_alamo + travel_time_nb_to_as)  # Arrival time at Alamo Square
solver.add(depart_alamo >= arrival_time_nb)  # Must leave after arriving at North Beach
solver.add(depart_alamo <= emily_end - meeting_duration)  # Must leave in time to meet for 15 minutes
solver.add(arrive_alamo >= emily_start)  # Must arrive at or after Emily starts being available
solver.add(depart_emily >= arrive_alamo + meeting_duration)  # Must leave after meeting for 15 minutes

# Maximize the meeting time with Emily (ideally want to meet her for 15 minutes)
meet_time = min(depart_emily - arrive_alamo, meeting_duration)

# We want to maximize the meeting time
solver.maximize(meet_time)

# Check if the solution is satisfiable and output the result
if solver.check() == sat:
    model = solver.model()
    depart_alamo_val = model[depart_alamo].as_decimal(2)
    arrive_alamo_val = model[arrive_alamo].as_decimal(2)
    depart_emily_val = model[depart_emily].as_decimal(2)

    print(f"Depart from North Beach to Alamo Square at: {depart_alamo_val} hours")
    print(f"Arrive at Alamo Square at: {arrive_alamo_val} hours")
    print(f"Depart from Alamo Square after meeting Emily at: {depart_emily_val} hours")
else:
    print("No valid schedule found.")