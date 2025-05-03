from z3 import *

# Initialize the Z3 solver
solver = Solver()

# Define the time variables
depart_fishermans = Real('depart_fishermans')  # Time you leave Pacific Heights to head to Fisherman's Wharf
arrive_fishermans = Real('arrive_fishermans')  # Time you arrive at Fisherman's Wharf
depart_david = Real('depart_david')              # Time you leave Fisherman's Wharf after meeting David

# Constants
travel_time_pacific_to_fw = 13  # minutes from Pacific Heights to Fisherman's Wharf
travel_time_fw_to_pacific = 12   # minutes from Fisherman's Wharf to Pacific Heights
meeting_duration = 15             # minimum meeting duration (in minutes)
david_start = 11.5               # 11:30 AM in hours
david_end = 14.75                 # 2:45 PM in hours
arrival_time_pacific = 9.0        # 9:00 AM in hours

# Constraints
solver.add(arrive_fishermans == depart_fishermans + travel_time_pacific_to_fw)  # Arrival time at Fisherman's Wharf
solver.add(depart_fishermans >= arrival_time_pacific)  # Must leave after arriving at Pacific Heights
solver.add(depart_fishermans <= david_end - (meeting_duration / 60))  # Must leave in time to meet for 15 minutes
solver.add(arrive_fishermans >= david_start)  # Must arrive at or after David starts being available
solver.add(depart_david >= arrive_fishermans + (meeting_duration / 60))  # Must leave after meeting for 15 minutes

# Maximize the meeting time with David (ideally want to meet him for at least 15 minutes)
meet_time = min(depart_david - arrive_fishermans, meeting_duration / 60)

# We want to maximize the meeting time
solver.maximize(meet_time)

# Check if the solution is satisfiable and output the result
if solver.check() == sat:
    model = solver.model()
    depart_fishermans_val = model[depart_fishermans].as_decimal(2)
    arrive_fishermans_val = model[arrive_fishermans].as_decimal(2)
    depart_david_val = model[depart_david].as_decimal(2)

    print(f"Depart from Pacific Heights to Fisherman's Wharf at: {depart_fishermans_val} hours")
    print(f"Arrive at Fisherman's Wharf at: {arrive_fishermans_val} hours")
    print(f"Depart from Fisherman's Wharf after meeting David at: {depart_david_val} hours")
else:
    print("No valid schedule found.")