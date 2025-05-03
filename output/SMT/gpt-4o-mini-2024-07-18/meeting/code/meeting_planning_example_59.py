from z3 import *

# Initialize the Z3 solver
solver = Solver()

# Define the time variables
depart_haight = Real('depart_haight')  # Time you leave Bayview to head to Haight-Ashbury
arrive_haight = Real('arrive_haight')  # Time you arrive at Haight-Ashbury
depart_richard = Real('depart_richard')  # Time you leave Haight-Ashbury after meeting Richard

# Constants
travel_time_bayview_to_haight = 19  # minutes from Bayview to Haight-Ashbury
travel_time_haight_to_bayview = 18   # minutes from Haight-Ashbury back to Bayview
meeting_duration = 105                # minimum meeting duration (in minutes)
richard_start = 7.0                  # 7:00 AM in hours
richard_end = 15.75                   # 3:45 PM in hours
arrival_time_bayview = 9.0            # 9:00 AM in hours

# Constraints
solver.add(arrive_haight == depart_haight + travel_time_bayview_to_haight)  # Arrival time at Haight-Ashbury
solver.add(depart_haight >= arrival_time_bayview)  # Must leave after arriving at Bayview
solver.add(depart_haight <= richard_end - (meeting_duration / 60))  # Must leave in time to meet for 105 minutes
solver.add(arrive_haight >= richard_start)  # Must arrive at or after Richard starts being available
solver.add(depart_richard >= arrive_haight + (meeting_duration / 60))  # Must leave after meeting for 105 minutes

# Maximize the meeting time with Richard (ideally want to meet him for 105 minutes)
meet_time = min(depart_richard - arrive_haight, meeting_duration / 60)

# We want to maximize the meeting time
solver.maximize(meet_time)

# Check if the solution is satisfiable and output the result
if solver.check() == sat:
    model = solver.model()
    depart_haight_val = model[depart_haight].as_decimal(2)
    arrive_haight_val = model[arrive_haight].as_decimal(2)
    depart_richard_val = model[depart_richard].as_decimal(2)

    print(f"Depart from Bayview to Haight-Ashbury at: {depart_haight_val} hours")
    print(f"Arrive at Haight-Ashbury at: {arrive_haight_val} hours")
    print(f"Depart from Haight-Ashbury after meeting Richard at: {depart_richard_val} hours")
else:
    print("No valid schedule found.")