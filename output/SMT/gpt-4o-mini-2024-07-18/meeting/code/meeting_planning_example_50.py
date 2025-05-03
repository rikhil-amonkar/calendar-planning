from z3 import *

# Initialize the Z3 solver
solver = Solver()

# Define the time variables
depart_nob_hill = Real('depart_nob_hill')  # Time you leave North Beach to head to Nob Hill
arrive_nob_hill = Real('arrive_nob_hill')  # Time you arrive at Nob Hill
depart_melissa = Real('depart_melissa')     # Time you leave Nob Hill after meeting Melissa

# Constants
travel_time_nb_to_nh = 7   # minutes from North Beach to Nob Hill
travel_time_nh_to_nb = 8    # minutes from Nob Hill to North Beach
meeting_duration = 75        # minimum meeting duration (in minutes)
melissa_start = 9.5         # 9:30 AM in hours
melissa_end = 20.5          # 8:30 PM in hours
arrival_time_nb = 9.0       # 9:00 AM in hours

# Constraints
solver.add(arrive_nob_hill == depart_nob_hill + travel_time_nb_to_nh)  # Arrival time at Nob Hill
solver.add(depart_nob_hill >= arrival_time_nb)  # Must leave after arriving at North Beach
solver.add(depart_nob_hill <= melissa_end - meeting_duration / 60)  # Must leave in time to meet for 75 minutes
solver.add(arrive_nob_hill >= melissa_start)  # Must arrive at or after Melissa starts being available
solver.add(depart_melissa >= arrive_nob_hill + meeting_duration / 60)  # Must leave after meeting for 75 minutes

# Maximize the meeting time with Melissa (ideally want to meet her for 75 minutes)
meet_time = min(depart_melissa - arrive_nob_hill, meeting_duration / 60)  # in hours

# We want to maximize the meeting time
solver.maximize(meet_time)

# Check if the solution is satisfiable and output the result
if solver.check() == sat:
    model = solver.model()
    depart_nob_hill_val = model[depart_nob_hill].as_decimal(2)
    arrive_nob_hill_val = model[arrive_nob_hill].as_decimal(2)
    depart_melissa_val = model[depart_melissa].as_decimal(2)

    print(f"Depart from North Beach to Nob Hill at: {depart_nob_hill_val} hours")
    print(f"Arrive at Nob Hill at: {arrive_nob_hill_val} hours")
    print(f"Depart from Nob Hill after meeting Melissa at: {depart_melissa_val} hours")
else:
    print("No valid schedule found.")