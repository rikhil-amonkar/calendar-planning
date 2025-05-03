from z3 import *

# Initialize the Z3 solver
solver = Solver()

# Define the time variables
depart_fishermans = Real('depart_fishermans')  # Time you leave Pacific Heights to head to Fisherman's Wharf
arrive_fishermans = Real('arrive_fishermans')  # Time you arrive at Fisherman's Wharf
depart_betty = Real('depart_betty')              # Time you leave Fisherman's Wharf after meeting with Betty

# Constants
travel_time_ph_to_fw = 13  # minutes from Pacific Heights to Fisherman's Wharf
travel_time_fw_to_ph = 12   # minutes from Fisherman's Wharf to Pacific Heights
meeting_duration = 105       # minutes
betty_start = 8.75          # 8:45 AM in hours
betty_end = 18.0            # 6:00 PM in hours
arrival_time_ph = 9.0       # 9:00 AM in hours

# Constraints
solver.add(arrive_fishermans == depart_fishermans + travel_time_ph_to_fw)  # Arrival time at Fisherman's Wharf
solver.add(depart_fishermans >= arrival_time_ph)  # Must leave after arriving at Pacific Heights
solver.add(depart_fishermans <= betty_end - meeting_duration)  # Must leave in time to meet for 105 minutes
solver.add(arrive_fishermans >= betty_start)  # Must arrive at or after Betty starts being available
solver.add(depart_betty >= arrive_fishermans + meeting_duration)  # Must leave after meeting for 105 minutes

# Maximize the meeting time with Betty (ideally want to meet her for 105 minutes)
meet_time = min(depart_betty - arrive_fishermans, meeting_duration)

# We want to maximize the meeting time
solver.maximize(meet_time)

# Check if the solution is satisfiable and output the result
if solver.check() == sat:
    model = solver.model()
    depart_fishermans_val = model[depart_fishermans].as_decimal(2)
    arrive_fishermans_val = model[arrive_fishermans].as_decimal(2)
    depart_betty_val = model[depart_betty].as_decimal(2)

    print(f"Depart from Pacific Heights to Fisherman's Wharf at: {depart_fishermans_val} hours")
    print(f"Arrive at Fisherman's Wharf at: {arrive_fishermans_val} hours")
    print(f"Depart from Fisherman's Wharf after meeting Betty at: {depart_betty_val} hours")
else:
    print("No valid schedule found.")