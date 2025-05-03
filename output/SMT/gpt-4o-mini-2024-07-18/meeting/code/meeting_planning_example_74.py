from z3 import *

# Initialize the Z3 solver
solver = Solver()

# Define the time variables
depart_nob = Real('depart_nob')      # Time you leave Richmond District to head to Nob Hill
arrive_nob = Real('arrive_nob')      # Time you arrive at Nob Hill
depart_richard = Real('depart_richard')  # Time you leave Nob Hill after meeting Richard

# Constants
travel_time_richmond_to_nob = 17    # minutes from Richmond District to Nob Hill
travel_time_nob_to_richmond = 14     # minutes from Nob Hill back to Richmond District
meeting_duration = 45                 # minimum meeting duration (in minutes)
richard_start = 16.0                 # 4:00 PM in hours
richard_end = 18.25                  # 6:15 PM in hours
arrival_time_richmond = 9.0          # 9:00 AM in hours

# Constraints
solver.add(arrive_nob == depart_nob + travel_time_richmond_to_nob)  # Arrival time at Nob Hill
solver.add(depart_nob >= arrival_time_richmond)  # Must leave after arriving at Richmond District
solver.add(depart_nob <= richard_end - (meeting_duration / 60))  # Must leave in time to meet for 45 minutes
solver.add(arrive_nob >= richard_start)  # Must arrive at or after Richard starts being available
solver.add(depart_richard >= arrive_nob + (meeting_duration / 60))  # Must leave after meeting for 45 minutes

# Maximize the meeting time with Richard (ideally want to meet him for at least 45 minutes)
meet_time = min(depart_richard - arrive_nob, meeting_duration / 60)

# We want to maximize the meeting time
solver.maximize(meet_time)

# Check if the solution is satisfiable and output the result
if solver.check() == sat:
    model = solver.model()
    depart_nob_val = model[depart_nob].as_decimal(2)
    arrive_nob_val = model[arrive_nob].as_decimal(2)
    depart_richard_val = model[depart_richard].as_decimal(2)

    print(f"Depart from Richmond District to Nob Hill at: {depart_nob_val} hours")
    print(f"Arrive at Nob Hill at: {arrive_nob_val} hours")
    print(f"Depart from Nob Hill after meeting Richard at: {depart_richard_val} hours")
else:
    print("No valid schedule found.")