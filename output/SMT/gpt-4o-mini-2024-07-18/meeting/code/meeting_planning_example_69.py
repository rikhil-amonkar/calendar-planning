from z3 import *

# Initialize the Z3 solver
solver = Solver()

# Define the time variables
depart_union = Real('depart_union')  # Time you leave Chinatown to head to Union Square
arrive_union = Real('arrive_union')  # Time you arrive at Union Square
depart_mark = Real('depart_mark')     # Time you leave Union Square after meeting Mark

# Constants
travel_time_chinatown_to_union = 7  # minutes from Chinatown to Union Square
travel_time_union_to_chinatown = 7   # minutes from Union Square to Chinatown
meeting_duration = 90                 # minimum meeting duration (in minutes)
mark_start = 8.0                     # 8:00 AM in hours
mark_end = 12.75                     # 12:45 PM in hours
arrival_time_chinatown = 9.0         # 9:00 AM in hours

# Constraints
solver.add(arrive_union == depart_union + travel_time_chinatown_to_union)  # Arrival time at Union Square
solver.add(depart_union >= arrival_time_chinatown)  # Must leave after arriving at Chinatown
solver.add(depart_union <= mark_end - (meeting_duration / 60))  # Must leave in time to meet for 90 minutes
solver.add(arrive_union >= mark_start)  # Must arrive at or after Mark starts being available
solver.add(depart_mark >= arrive_union + (meeting_duration / 60))  # Must leave after meeting for 90 minutes

# Maximize the meeting time with Mark (ideally want to meet him for at least 90 minutes)
meet_time = min(depart_mark - arrive_union, meeting_duration / 60)

# We want to maximize the meeting time
solver.maximize(meet_time)

# Check if the solution is satisfiable and output the result
if solver.check() == sat:
    model = solver.model()
    depart_union_val = model[depart_union].as_decimal(2)
    arrive_union_val = model[arrive_union].as_decimal(2)
    depart_mark_val = model[depart_mark].as_decimal(2)

    print(f"Depart from Chinatown to Union Square at: {depart_union_val} hours")
    print(f"Arrive at Union Square at: {arrive_union_val} hours")
    print(f"Depart from Union Square after meeting Mark at: {depart_mark_val} hours")
else:
    print("No valid schedule found.")