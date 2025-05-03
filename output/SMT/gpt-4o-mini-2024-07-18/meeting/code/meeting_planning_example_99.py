from z3 import *

# Initialize the Z3 solver
solver = Solver()

# Define the time variables
depart_union = Real('depart_union')     # Time you leave Fisherman's Wharf to head to Union Square
arrive_union = Real('arrive_union')     # Time you arrive at Union Square
depart_kevin = Real('depart_kevin')      # Time you leave Union Square after meeting Kevin

# Constants
travel_time_wharf_to_union = 13         # minutes from Fisherman's Wharf to Union Square
travel_time_union_to_wharf = 15          # minutes from Union Square to Fisherman's Wharf
meeting_duration = 15                     # minimum meeting duration (in minutes)
kevin_start = 13 + 15 / 60               # 1:15 PM in hours
kevin_end = 19 + 15 / 60                 # 7:15 PM in hours
arrival_time_wharf = 9.0                  # 9:00 AM in hours

# Constraints
solver.add(arrive_union == depart_union + travel_time_wharf_to_union)  # Arrival time at Union Square
solver.add(depart_union >= arrival_time_wharf)  # Must leave after arriving at Fisherman's Wharf
solver.add(depart_union <= kevin_end - (meeting_duration / 60))  # Must leave in time to meet for 15 minutes
solver.add(arrive_union >= kevin_start)  # Must arrive at or after Kevin starts being available
solver.add(depart_kevin >= arrive_union + (meeting_duration / 60))  # Must leave after meeting for 15 minutes

# Maximize the meeting time with Kevin (ideally want to meet him for at least 15 minutes)
meet_time = min(depart_kevin - arrive_union, meeting_duration / 60)

# We want to maximize the meeting time
solver.maximize(meet_time)

# Check if the solution is satisfiable and output the result
if solver.check() == sat:
    model = solver.model()
    depart_union_val = model[depart_union].as_decimal(2)
    arrive_union_val = model[arrive_union].as_decimal(2)
    depart_kevin_val = model[depart_kevin].as_decimal(2)

    print(f"Depart from Fisherman's Wharf to Union Square at: {depart_union_val} hours")
    print(f"Arrive at Union Square at: {arrive_union_val} hours")
    print(f"Depart from Union Square after meeting Kevin at: {depart_kevin_val} hours")
else:
    print("No valid schedule found.")