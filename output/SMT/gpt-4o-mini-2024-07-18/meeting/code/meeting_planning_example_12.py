from z3 import *

# Initialize the Z3 solver
solver = Solver()

# Define the time variables
depart_alamo = Real('depart_alamo')  # Time at which we leave North Beach to head to Alamo Square
arrive_alamo = Real('arrive_alamo')  # Time at which we arrive at Alamo Square
depart_barbara = Real('depart_barbara')  # Time we leave Alamo Square after meeting with Barbara

# Constants
travel_time_north_beach_to_alamo = 16  # minutes
meeting_duration = 90  # minutes
barbara_start = 18.0   # 6:00 PM in hours
barbara_end = 21.5     # 9:30 PM in hours
arrival_time_north_beach = 9.0  # 9:00 AM in hours

# Constraints
solver.add(arrive_alamo == depart_alamo + travel_time_north_beach_to_alamo)
solver.add(depart_alamo >= arrival_time_north_beach)  # Must leave after arriving at North Beach
solver.add(depart_alamo <= barbara_end - meeting_duration)  # Must leave in time to meet for 90 minutes
solver.add(arrive_alamo >= barbara_start)  # Must arrive at or after Barbara starts being available
solver.add(depart_barbara >= arrive_alamo + meeting_duration)  # Must leave after meeting for 90 minutes

# Maximize the meeting time with Barbara (ideally want to meet her for 90 minutes)
meet_time = min(depart_barbara - arrive_alamo, meeting_duration)

# We want to maximize the meeting time
solver.maximize(meet_time)

# Check if the solution is satisfiable and output the result
if solver.check() == sat:
    model = solver.model()
    depart_alamo_val = model[depart_alamo].as_decimal(2)
    arrive_alamo_val = model[arrive_alamo].as_decimal(2)
    depart_barbara_val = model[depart_barbara].as_decimal(2)
    
    print(f"Depart from North Beach to Alamo Square at: {depart_alamo_val} hours")
    print(f"Arrive at Alamo Square at: {arrive_alamo_val} hours")
    print(f"Depart from Alamo Square after meeting Barbara at: {depart_barbara_val} hours")
else:
    print("No valid schedule found.")