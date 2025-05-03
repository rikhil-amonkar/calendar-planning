from z3 import *

# Initialize the Z3 solver
solver = Solver()

# Define the time variables
depart_financial = Real('depart_financial')  # Time you leave The Castro to head to the Financial District
arrive_financial = Real('arrive_financial')  # Time you arrive at the Financial District
depart_nancy = Real('depart_nancy')           # Time you leave the Financial District after meeting Nancy

# Constants
travel_time_castro_to_fd = 20  # minutes from The Castro to Financial District
travel_time_fd_to_castro = 23   # minutes from Financial District to The Castro
meeting_duration = 30            # minimum meeting duration (in minutes)
nancy_start = 9.25              # 9:15 AM in hours
nancy_end = 16.75                # 4:45 PM in hours
arrival_time_castro = 9.0       # 9:00 AM in hours

# Constraints
solver.add(arrive_financial == depart_financial + travel_time_castro_to_fd)  # Arrival time at Financial District
solver.add(depart_financial >= arrival_time_castro)  # Must leave after arriving at The Castro
solver.add(depart_financial <= nancy_end - (meeting_duration / 60))  # Must leave in time to meet for 30 minutes
solver.add(arrive_financial >= nancy_start)  # Must arrive at or after Nancy starts being available
solver.add(depart_nancy >= arrive_financial + (meeting_duration / 60))  # Must leave after meeting for 30 minutes

# Maximize the meeting time with Nancy (ideally want to meet her for 30 minutes)
meet_time = min(depart_nancy - arrive_financial, meeting_duration / 60)

# We want to maximize the meeting time
solver.maximize(meet_time)

# Check if the solution is satisfiable and output the result
if solver.check() == sat:
    model = solver.model()
    depart_financial_val = model[depart_financial].as_decimal(2)
    arrive_financial_val = model[arrive_financial].as_decimal(2)
    depart_nancy_val = model[depart_nancy].as_decimal(2)

    print(f"Depart from The Castro to Financial District at: {depart_financial_val} hours")
    print(f"Arrive at Financial District at: {arrive_financial_val} hours")
    print(f"Depart from Financial District after meeting Nancy at: {depart_nancy_val} hours")
else:
    print("No valid schedule found.")