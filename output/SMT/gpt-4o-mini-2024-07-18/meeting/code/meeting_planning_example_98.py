from z3 import *

# Initialize the Z3 solver
solver = Solver()

# Define the time variables
depart_richmond = Real('depart_richmond')  # Time you leave Alamo Square to head to Richmond District
arrive_richmond = Real('arrive_richmond')  # Time you arrive at Richmond District
depart_timothy = Real('depart_timothy')    # Time you leave Richmond District after meeting Timothy

# Constants
travel_time_alamo_to_richmond = 12        # minutes from Alamo Square to Richmond District
travel_time_richmond_to_alamo = 13         # minutes from Richmond District to Alamo Square
meeting_duration = 45                      # minimum meeting duration (in minutes)
timothy_start = 20.75                      # 8:45 PM in hours
timothy_end = 21.5                         # 9:30 PM in hours
arrival_time_alamo = 9.0                   # 9:00 AM in hours

# Constraints
solver.add(arrive_richmond == depart_richmond + travel_time_alamo_to_richmond)  # Arrival time at Richmond District
solver.add(depart_richmond >= arrival_time_alamo)  # Must leave after arriving at Alamo Square
solver.add(depart_richmond <= timothy_end - (meeting_duration / 60))  # Must leave in time to meet for 45 minutes
solver.add(arrive_richmond >= timothy_start)  # Must arrive at or after Timothy starts being available
solver.add(depart_timothy >= arrive_richmond + (meeting_duration / 60))  # Must leave after meeting for 45 minutes

# Maximize the meeting time with Timothy (ideally we want to meet him for at least 45 minutes)
meet_time = min(depart_timothy - arrive_richmond, meeting_duration / 60)

# We want to maximize the meeting time
solver.maximize(meet_time)

# Check if the solution is satisfiable and output the result
if solver.check() == sat:
    model = solver.model()
    depart_richmond_val = model[depart_richmond].as_decimal(2)
    arrive_richmond_val = model[arrive_richmond].as_decimal(2)
    depart_timothy_val = model[depart_timothy].as_decimal(2)

    print(f"Depart from Alamo Square to Richmond District at: {depart_richmond_val} hours")
    print(f"Arrive at Richmond District at: {arrive_richmond_val} hours")
    print(f"Depart from Richmond District after meeting Timothy at: {depart_timothy_val} hours")
else:
    print("No valid schedule found.")