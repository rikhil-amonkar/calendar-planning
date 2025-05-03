from z3 import *

# Initialize the Z3 solver
solver = Solver()

# Define the time variables
depart_richmond = Real('depart_richmond')  # Time you leave Chinatown to head to Richmond District
arrive_richmond = Real('arrive_richmond')  # Time you arrive at Richmond District
depart_charles = Real('depart_charles')    # Time you leave Richmond District after meeting Charles

# Constants
travel_time_chinatown_to_richmond = 20     # minutes from Chinatown to Richmond District
travel_time_richmond_to_chinatown = 20      # minutes from Richmond District back to Chinatown
meeting_duration = 75                       # minimum meeting duration (in minutes)
charles_start = 18.0                       # 6:00 PM in hours
charles_end = 21.0                         # 9:00 PM in hours
arrival_time_chinatown = 9.0                # 9:00 AM in hours

# Constraints
solver.add(arrive_richmond == depart_richmond + travel_time_chinatown_to_richmond)  # Arrival time at Richmond District
solver.add(depart_richmond >= arrival_time_chinatown)  # Must leave after arriving at Chinatown
solver.add(depart_richmond <= charles_end - (meeting_duration / 60))  # Must leave in time to meet for 75 minutes
solver.add(arrive_richmond >= charles_start)  # Must arrive at or after Charles starts being available
solver.add(depart_charles >= arrive_richmond + (meeting_duration / 60))  # Must leave after meeting for 75 minutes

# Maximize the meeting time with Charles (ideally we want to meet him for at least 75 minutes)
meet_time = min(depart_charles - arrive_richmond, meeting_duration / 60)

# We want to maximize the meeting time
solver.maximize(meet_time)

# Check if the solution is satisfiable and output the result
if solver.check() == sat:
    model = solver.model()
    depart_richmond_val = model[depart_richmond].as_decimal(2)
    arrive_richmond_val = model[arrive_richmond].as_decimal(2)
    depart_charles_val = model[depart_charles].as_decimal(2)

    print(f"Depart from Chinatown to Richmond District at: {depart_richmond_val} hours")
    print(f"Arrive at Richmond District at: {arrive_richmond_val} hours")
    print(f"Depart from Richmond District after meeting Charles at: {depart_charles_val} hours")
else:
    print("No valid schedule found.")