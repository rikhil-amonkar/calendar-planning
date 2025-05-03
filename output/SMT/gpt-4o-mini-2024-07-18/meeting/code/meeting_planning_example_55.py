from z3 import *

# Initialize the Z3 solver
solver = Solver()

# Define the time variables
depart_nob_hill = Real('depart_nob_hill')  # Time you leave Financial District to head to Nob Hill
arrive_nob_hill = Real('arrive_nob_hill')  # Time you arrive at Nob Hill
depart_helen = Real('depart_helen')          # Time you leave Nob Hill after meeting Helen

# Constants
travel_time_fd_to_nh = 8   # minutes from Financial District to Nob Hill
travel_time_nh_to_fd = 9    # minutes from Nob Hill back to Financial District
meeting_duration = 45        # minimum meeting duration (in minutes)
helen_start = 11.5          # 11:30 AM in hours
helen_end = 12.25           # 12:15 PM in hours
arrival_time_fd = 9.0       # 9:00 AM in hours

# Constraints
solver.add(arrive_nob_hill == depart_nob_hill + travel_time_fd_to_nh)  # Arrival time at Nob Hill
solver.add(depart_nob_hill >= arrival_time_fd)  # Must leave after arriving at Financial District
solver.add(depart_nob_hill <= helen_end - (meeting_duration / 60))  # Must leave in time to meet for 45 minutes
solver.add(arrive_nob_hill >= helen_start)  # Must arrive at or after Helen starts being available
solver.add(depart_helen >= arrive_nob_hill + (meeting_duration / 60))  # Must leave after meeting for 45 minutes

# Maximize the meeting time with Helen (ideally want to meet her for 45 minutes)
meet_time = min(depart_helen - arrive_nob_hill, meeting_duration / 60)

# We want to maximize the meeting time
solver.maximize(meet_time)

# Check if the solution is satisfiable and output the result
if solver.check() == sat:
    model = solver.model()
    depart_nob_hill_val = model[depart_nob_hill].as_decimal(2)
    arrive_nob_hill_val = model[arrive_nob_hill].as_decimal(2)
    depart_helen_val = model[depart_helen].as_decimal(2)

    print(f"Depart from Financial District to Nob Hill at: {depart_nob_hill_val} hours")
    print(f"Arrive at Nob Hill at: {arrive_nob_hill_val} hours")
    print(f"Depart from Nob Hill after meeting Helen at: {depart_helen_val} hours")
else:
    print("No valid schedule found.")