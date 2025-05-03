from z3 import *

# Initialize the Z3 solver
solver = Solver()

# Define the time variables
depart_haight = Real('depart_haight')  # Time you leave Marina District to head to Haight-Ashbury
arrive_haight = Real('arrive_haight')  # Time you arrive at Haight-Ashbury
depart_timothy = Real('depart_timothy') # Time you leave Haight-Ashbury after meeting Timothy

# Constants
travel_time_marina_to_haight = 16  # minutes from Marina District to Haight-Ashbury
travel_time_haight_to_marina = 17   # minutes from Haight-Ashbury to Marina District
meeting_duration = 60                # minimum meeting duration (in minutes)
timothy_start = 17.0                # 5:00 PM in hours
timothy_end = 20.25                  # 8:15 PM in hours
arrival_time_marina = 9.0            # 9:00 AM in hours

# Constraints
solver.add(arrive_haight == depart_haight + travel_time_marina_to_haight)  # Arrival time at Haight-Ashbury
solver.add(depart_haight >= arrival_time_marina)  # Must leave after arriving at Marina District
solver.add(depart_haight <= timothy_end - (meeting_duration / 60))  # Must leave in time to meet for 60 minutes
solver.add(arrive_haight >= timothy_start)  # Must arrive at or after Timothy starts being available
solver.add(depart_timothy >= arrive_haight + (meeting_duration / 60))  # Must leave after meeting for 60 minutes

# Maximize the meeting time with Timothy (ideally want to meet him for at least 60 minutes)
meet_time = min(depart_timothy - arrive_haight, meeting_duration / 60)

# We want to maximize the meeting time
solver.maximize(meet_time)

# Check if the solution is satisfiable and output the result
if solver.check() == sat:
    model = solver.model()
    depart_haight_val = model[depart_haight].as_decimal(2)
    arrive_haight_val = model[arrive_haight].as_decimal(2)
    depart_timothy_val = model[depart_timothy].as_decimal(2)

    print(f"Depart from Marina District to Haight-Ashbury at: {depart_haight_val} hours")
    print(f"Arrive at Haight-Ashbury at: {arrive_haight_val} hours")
    print(f"Depart from Haight-Ashbury after meeting Timothy at: {depart_timothy_val} hours")
else:
    print("No valid schedule found.")