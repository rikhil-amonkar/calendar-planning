from z3 import *

# Initialize the Z3 solver
solver = Solver()

# Define the time variables
depart_castro = Real('depart_castro')  # Time you leave Union Square to head to The Castro
arrive_castro = Real('arrive_castro')  # Time you arrive at The Castro
depart_michelle = Real('depart_michelle')  # Time you leave The Castro after meeting Michelle

# Constants
travel_time_union_to_castro = 19  # minutes from Union Square to The Castro
travel_time_castro_to_union = 19   # minutes from The Castro to Union Square
meeting_duration = 105              # minimum meeting duration (in minutes)
michelle_start = 18.0              # 6:00 PM in hours
michelle_end = 20.0                # 8:00 PM in hours
arrival_time_union = 9.0           # 9:00 AM in hours

# Constraints
solver.add(arrive_castro == depart_castro + travel_time_union_to_castro)  # Arrival time at The Castro
solver.add(depart_castro >= arrival_time_union)  # Must leave after arriving at Union Square
solver.add(depart_castro <= michelle_end - (meeting_duration / 60))  # Must leave in time to meet for 105 minutes
solver.add(arrive_castro >= michelle_start)  # Must arrive at or after Michelle starts being available
solver.add(depart_michelle >= arrive_castro + (meeting_duration / 60))  # Must leave after meeting for 105 minutes

# Maximize the meeting time with Michelle (ideally want to meet her for at least 105 minutes)
meet_time = min(depart_michelle - arrive_castro, meeting_duration / 60)

# We want to maximize the meeting time
solver.maximize(meet_time)

# Check if the solution is satisfiable and output the result
if solver.check() == sat:
    model = solver.model()
    depart_castro_val = model[depart_castro].as_decimal(2)
    arrive_castro_val = model[arrive_castro].as_decimal(2)
    depart_michelle_val = model[depart_michelle].as_decimal(2)

    print(f"Depart from Union Square to The Castro at: {depart_castro_val} hours")
    print(f"Arrive at The Castro at: {arrive_castro_val} hours")
    print(f"Depart from The Castro after meeting Michelle at: {depart_michelle_val} hours")
else:
    print("No valid schedule found.")