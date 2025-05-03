from z3 import *

# Initialize the Z3 solver
solver = Solver()

# Define the time variables
depart_union = Real('depart_union')  # Time at which we leave Presidio to head to Union Square
arrive_union = Real('arrive_union')  # Time at which we arrive at Union Square
depart_andrew = Real('depart_andrew')  # Time we leave Union Square after meeting Andrew

# Constants
travel_time_presidio_to_union = 22  # minutes
travel_time_union_to_presidio = 24   # minutes
meeting_duration = 105                # minutes
andrew_start = 11.25                 # 11:15 AM in hours
andrew_end = 17.25                   # 5:15 PM in hours
arrival_time_presidio = 9.0          # 9:00 AM in hours

# Constraints
solver.add(arrive_union == depart_union + travel_time_presidio_to_union)
solver.add(depart_union >= arrival_time_presidio)  # Must leave after arriving at Presidio
solver.add(depart_union <= andrew_end - meeting_duration)  # Must leave in time to meet for 105 minutes
solver.add(arrive_union >= andrew_start)  # Must arrive at or after Andrew starts being available
solver.add(depart_andrew >= arrive_union + meeting_duration)  # Must leave after meeting for 105 minutes

# Maximize the meeting time with Andrew (ideally want to meet him for 105 minutes)
meet_time = min(depart_andrew - arrive_union, meeting_duration)

# We want to maximize the meeting time
solver.maximize(meet_time)

# Check if the solution is satisfiable and output the result
if solver.check() == sat:
    model = solver.model()
    depart_union_val = model[depart_union].as_decimal(2)
    arrive_union_val = model[arrive_union].as_decimal(2)
    depart_andrew_val = model[depart_andrew].as_decimal(2)

    print(f"Depart from Presidio to Union Square at: {depart_union_val} hours")
    print(f"Arrive at Union Square at: {arrive_union_val} hours")
    print(f"Depart from Union Square after meeting Andrew at: {depart_andrew_val} hours")
else:
    print("No valid schedule found.")