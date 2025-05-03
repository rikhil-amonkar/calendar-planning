from z3 import *

# Initialize the Z3 solver
solver = Solver()

# Define the time variables
depart_alamo = Real('depart_alamo')  # Time you leave Pacific Heights to head to Alamo Square
arrive_alamo = Real('arrive_alamo')  # Time you arrive at Alamo Square
depart_john = Real('depart_john')     # Time you leave Alamo Square after meeting John

# Constants
travel_time_pacific_to_alamo = 10  # minutes from Pacific Heights to Alamo Square
travel_time_alamo_to_pacific = 10   # minutes from Alamo Square to Pacific Heights
meeting_duration = 90                # minimum meeting duration (in minutes)
john_start = 9.75                   # 9:45 AM in hours
john_end = 14.5                     # 2:30 PM in hours
arrival_time_pacific = 9.0           # 9:00 AM in hours

# Constraints
solver.add(arrive_alamo == depart_alamo + travel_time_pacific_to_alamo)  # Arrival time at Alamo Square
solver.add(depart_alamo >= arrival_time_pacific)  # Must leave after arriving at Pacific Heights
solver.add(depart_alamo <= john_end - (meeting_duration / 60))  # Must leave in time to meet for 90 minutes
solver.add(arrive_alamo >= john_start)  # Must arrive at or after John starts being available
solver.add(depart_john >= arrive_alamo + (meeting_duration / 60))  # Must leave after meeting for 90 minutes

# Maximize the meeting time with John (ideally want to meet him for at least 90 minutes)
meet_time = min(depart_john - arrive_alamo, meeting_duration / 60)

# We want to maximize the meeting time
solver.maximize(meet_time)

# Check if the solution is satisfiable and output the result
if solver.check() == sat:
    model = solver.model()
    depart_alamo_val = model[depart_alamo].as_decimal(2)
    arrive_alamo_val = model[arrive_alamo].as_decimal(2)
    depart_john_val = model[depart_john].as_decimal(2)

    print(f"Depart from Pacific Heights to Alamo Square at: {depart_alamo_val} hours")
    print(f"Arrive at Alamo Square at: {arrive_alamo_val} hours")
    print(f"Depart from Alamo Square after meeting John at: {depart_john_val} hours")
else:
    print("No valid schedule found.")