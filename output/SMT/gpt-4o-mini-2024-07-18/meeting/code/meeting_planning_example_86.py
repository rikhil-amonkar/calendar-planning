from z3 import *

# Initialize the Z3 solver
solver = Solver()

# Define the time variables
depart_nob = Real('depart_nob')      # Time you leave Marina District to head to Nob Hill
arrive_nob = Real('arrive_nob')      # Time you arrive at Nob Hill
depart_daniel = Real('depart_daniel') # Time you leave Nob Hill after meeting Daniel

# Constants
travel_time_marina_to_nob = 12      # minutes from Marina District to Nob Hill
travel_time_nob_to_marina = 11       # minutes from Nob Hill to Marina District
meeting_duration = 15                 # minimum meeting duration (in minutes)
daniel_start = 19.75                  # 7:45 PM in hours
daniel_end = 21.0                     # 9:00 PM in hours
arrival_time_marina = 9.0             # 9:00 AM in hours

# Constraints
solver.add(arrive_nob == depart_nob + travel_time_marina_to_nob)  # Arrival time at Nob Hill
solver.add(depart_nob >= arrival_time_marina)  # Must leave after arriving at Marina District
solver.add(depart_nob <= daniel_end - (meeting_duration / 60))  # Must leave in time to meet for 15 minutes
solver.add(arrive_nob >= daniel_start)  # Must arrive at or after Daniel starts being available
solver.add(depart_daniel >= arrive_nob + (meeting_duration / 60))  # Must leave after meeting for 15 minutes

# Maximize the meeting time with Daniel (ideally we want to meet him for at least 15 minutes)
meet_time = min(depart_daniel - arrive_nob, meeting_duration / 60)

# We want to maximize the meeting time
solver.maximize(meet_time)

# Check if the solution is satisfiable and output the result
if solver.check() == sat:
    model = solver.model()
    depart_nob_val = model[depart_nob].as_decimal(2)
    arrive_nob_val = model[arrive_nob].as_decimal(2)
    depart_daniel_val = model[depart_daniel].as_decimal(2)

    print(f"Depart from Marina District to Nob Hill at: {depart_nob_val} hours")
    print(f"Arrive at Nob Hill at: {arrive_nob_val} hours")
    print(f"Depart from Nob Hill after meeting Daniel at: {depart_daniel_val} hours")
else:
    print("No valid schedule found.")