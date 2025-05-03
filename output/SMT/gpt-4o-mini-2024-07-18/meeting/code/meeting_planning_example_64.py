from z3 import *

# Initialize the Z3 solver
solver = Solver()

# Define the time variables
depart_pacific = Real('depart_pacific')  # Time you leave Nob Hill to head to Pacific Heights
arrive_pacific = Real('arrive_pacific')  # Time you arrive at Pacific Heights
depart_margaret = Real('depart_margaret')  # Time you leave Pacific Heights after meeting Margaret

# Constants
travel_time_nob_to_pacific = 8   # minutes from Nob Hill to Pacific Heights
travel_time_pacific_to_nob = 8    # minutes from Pacific Heights to Nob Hill
meeting_duration = 45               # minimum meeting duration (in minutes)
margaret_start = 15.75             # 3:45 PM in hours
margaret_end = 19.25               # 7:15 PM in hours
arrival_time_nob = 9.0             # 9:00 AM in hours

# Constraints
solver.add(arrive_pacific == depart_pacific + travel_time_nob_to_pacific)  # Arrival time at Pacific Heights
solver.add(depart_pacific >= arrival_time_nob)  # Must leave after arriving at Nob Hill
solver.add(depart_pacific <= margaret_end - (meeting_duration / 60))  # Must leave in time to meet for 45 minutes
solver.add(arrive_pacific >= margaret_start)  # Must arrive at or after Margaret starts being available
solver.add(depart_margaret >= arrive_pacific + (meeting_duration / 60))  # Must leave after meeting for 45 minutes

# Maximize the meeting time with Margaret (ideally want to meet her for 45 minutes)
meet_time = min(depart_margaret - arrive_pacific, meeting_duration / 60)

# We want to maximize the meeting time
solver.maximize(meet_time)

# Check if the solution is satisfiable and output the result
if solver.check() == sat:
    model = solver.model()
    depart_pacific_val = model[depart_pacific].as_decimal(2)
    arrive_pacific_val = model[arrive_pacific].as_decimal(2)
    depart_margaret_val = model[depart_margaret].as_decimal(2)

    print(f"Depart from Nob Hill to Pacific Heights at: {depart_pacific_val} hours")
    print(f"Arrive at Pacific Heights at: {arrive_pacific_val} hours")
    print(f"Depart from Pacific Heights after meeting Margaret at: {depart_margaret_val} hours")
else:
    print("No valid schedule found.")