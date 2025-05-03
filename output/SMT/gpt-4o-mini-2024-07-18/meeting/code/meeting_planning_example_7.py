from z3 import *

# Initialize the Z3 solver
solver = Solver()

# Define the time variables
depart_north_beach = Real('depart_north_beach')  # Time at which we leave Richmond District to head to North Beach
arrive_north_beach = Real('arrive_north_beach')  # Time at which we arrive at North Beach
depart_john = Real('depart_john')  # Time we leave North Beach after meeting with John

# Constants
travel_time_richmond_to_north_beach = 17  # minutes
travel_time_north_beach_to_richmond = 18   # minutes
meeting_duration = 75  # minutes
john_start = 15.25  # 3:15 PM in hours
john_end = 17.25    # 5:15 PM in hours
arrival_time_richmond = 9.0  # 9:00 AM in hours

# Constraints
solver.add(arrive_north_beach == depart_north_beach + travel_time_richmond_to_north_beach)
solver.add(depart_north_beach >= arrival_time_richmond)  # Must leave after arriving at Richmond District
solver.add(depart_north_beach <= john_end - meeting_duration)  # Must leave in time to meet for 75 minutes
solver.add(arrive_north_beach >= john_start)  # Must arrive at or after John starts being available
solver.add(depart_john >= arrive_north_beach + meeting_duration)  # Must leave after meeting for 75 minutes

# Maximize the meeting time with John (ideally want to meet him for 75 minutes)
meet_time = min(depart_john - arrive_north_beach, meeting_duration)

# We want to maximize the meeting time
solver.maximize(meet_time)

# Check if the solution is satisfiable and output the result
if solver.check() == sat:
    model = solver.model()
    depart_north_beach_val = model[depart_north_beach].as_decimal(2)
    arrive_north_beach_val = model[arrive_north_beach].as_decimal(2)
    depart_john_val = model[depart_john].as_decimal(2)
    
    print(f"Depart from Richmond District to North Beach at: {depart_north_beach_val} hours")
    print(f"Arrive at North Beach at: {arrive_north_beach_val} hours")
    print(f"Depart from North Beach after meeting John at: {depart_john_val} hours")
else:
    print("No valid schedule found.")