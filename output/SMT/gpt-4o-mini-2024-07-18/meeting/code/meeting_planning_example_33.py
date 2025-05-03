from z3 import *

# Initialize the Z3 solver
solver = Solver()

# Define the time variables
depart_union_square = Real('depart_union_square')  # Time we leave Sunset District to head to Union Square
arrive_union_square = Real('arrive_union_square')  # Time we arrive at Union Square
depart_sarah = Real('depart_sarah')                 # Time we leave Union Square after meeting Sarah

# Constants
travel_time_sunset_to_union = 30  # minutes
travel_time_union_to_sunset = 26   # minutes
meeting_duration = 15               # minutes
sarah_start = 12.5                  # 12:30 PM in hours
sarah_end = 21.5                    # 9:30 PM in hours
arrival_time_sunset = 9.0           # 9:00 AM in hours

# Constraints
solver.add(arrive_union_square == depart_union_square + travel_time_sunset_to_union)
solver.add(depart_union_square >= arrival_time_sunset)  # Must leave after arriving at Sunset District
solver.add(depart_union_square <= sarah_end - meeting_duration)  # Must leave in time to meet for 15 minutes
solver.add(arrive_union_square >= sarah_start)  # Must arrive at or after Sarah starts being available
solver.add(depart_sarah >= arrive_union_square + meeting_duration)  # Must leave after meeting for 15 minutes

# Maximize the meeting time with Sarah (ideally want to meet her for 15 minutes)
meet_time = min(depart_sarah - arrive_union_square, meeting_duration)

# We want to maximize the meeting time
solver.maximize(meet_time)

# Check if the solution is satisfiable and output the result
if solver.check() == sat:
    model = solver.model()
    depart_union_square_val = model[depart_union_square].as_decimal(2)
    arrive_union_square_val = model[arrive_union_square].as_decimal(2)
    depart_sarah_val = model[depart_sarah].as_decimal(2)

    print(f"Depart from Sunset District to Union Square at: {depart_union_square_val} hours")
    print(f"Arrive at Union Square at: {arrive_union_square_val} hours")
    print(f"Depart from Union Square after meeting Sarah at: {depart_sarah_val} hours")
else:
    print("No valid schedule found.")