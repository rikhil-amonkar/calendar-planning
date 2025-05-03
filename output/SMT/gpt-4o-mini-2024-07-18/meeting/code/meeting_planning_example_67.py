from z3 import *

# Initialize the Z3 solver
solver = Solver()

# Define the time variables
depart_financial = Real('depart_financial')  # Time you leave Golden Gate Park to head to Financial District
arrive_financial = Real('arrive_financial')  # Time you arrive at Financial District
depart_kenneth = Real('depart_kenneth')       # Time you leave Financial District after meeting Kenneth

# Constants
travel_time_ggp_to_fd = 26  # minutes from Golden Gate Park to Financial District
travel_time_fd_to_ggp = 23   # minutes from Financial District to Golden Gate Park
meeting_duration = 105        # minimum meeting duration (in minutes)
kenneth_start = 20.0         # 8:00 PM in hours
kenneth_end = 22.0           # 10:00 PM in hours
arrival_time_ggp = 9.0       # 9:00 AM in hours

# Constraints
solver.add(arrive_financial == depart_financial + travel_time_ggp_to_fd)  # Arrival time at Financial District
solver.add(depart_financial >= arrival_time_ggp)  # Must leave after arriving at Golden Gate Park
solver.add(depart_financial <= kenneth_end - (meeting_duration / 60))  # Must leave in time to meet for 105 minutes
solver.add(arrive_financial >= kenneth_start)  # Must arrive at or after Kenneth starts being available
solver.add(depart_kenneth >= arrive_financial + (meeting_duration / 60))  # Must leave after meeting for 105 minutes

# Maximize the meeting time with Kenneth (ideally want to meet him for 105 minutes)
meet_time = min(depart_kenneth - arrive_financial, meeting_duration / 60)

# We want to maximize the meeting time
solver.maximize(meet_time)

# Check if the solution is satisfiable and output the result
if solver.check() == sat:
    model = solver.model()
    depart_financial_val = model[depart_financial].as_decimal(2)
    arrive_financial_val = model[arrive_financial].as_decimal(2)
    depart_kenneth_val = model[depart_kenneth].as_decimal(2)

    print(f"Depart from Golden Gate Park to Financial District at: {depart_financial_val} hours")
    print(f"Arrive at Financial District at: {arrive_financial_val} hours")
    print(f"Depart from Financial District after meeting Kenneth at: {depart_kenneth_val} hours")
else:
    print("No valid schedule found.")