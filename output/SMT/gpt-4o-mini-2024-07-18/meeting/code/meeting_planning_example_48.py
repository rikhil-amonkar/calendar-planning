from z3 import *

# Initialize the Z3 solver
solver = Solver()

# Define the time variables
depart_union_square = Real('depart_union_square')  # Time you leave Financial District to head to Union Square
arrive_union_square = Real('arrive_union_square')  # Time you arrive at Union Square
depart_joseph = Real('depart_joseph')                # Time you leave Union Square after meeting Joseph

# Constants
travel_time_fd_to_us = 9   # Travel time from Financial District to Union Square (in minutes)
travel_time_us_to_fd = 9    # Travel time from Union Square to Financial District (in minutes)
meeting_duration = 15        # Minimum meeting duration (in minutes)
joseph_start = 21.5         # 9:30 PM in hours
joseph_end = 22.0           # 10:00 PM in hours
arrival_time_fd = 9.0       # 9:00 AM in hours

# Constraints
solver.add(arrive_union_square == depart_union_square + travel_time_fd_to_us)  # Arrival time at Union Square
solver.add(depart_union_square >= arrival_time_fd)  # Must leave after arriving at Financial District
solver.add(depart_union_square <= joseph_end - meeting_duration)  # Must leave in time to meet for 15 minutes
solver.add(arrive_union_square >= joseph_start)  # Must arrive at or after Joseph starts being available
solver.add(depart_joseph >= arrive_union_square + meeting_duration)  # Must leave after meeting for 15 minutes

# Maximize the meeting time with Joseph (ideally want to meet him for 15 minutes)
meet_time = min(depart_joseph - arrive_union_square, meeting_duration)

# We want to maximize the meeting time
solver.maximize(meet_time)

# Check if the solution is satisfiable and output the result
if solver.check() == sat:
    model = solver.model()
    depart_union_square_val = model[depart_union_square].as_decimal(2)
    arrive_union_square_val = model[arrive_union_square].as_decimal(2)
    depart_joseph_val = model[depart_joseph].as_decimal(2)

    print(f"Depart from Financial District to Union Square at: {depart_union_square_val} hours")
    print(f"Arrive at Union Square at: {arrive_union_square_val} hours")
    print(f"Depart from Union Square after meeting Joseph at: {depart_joseph_val} hours")
else:
    print("No valid schedule found.")