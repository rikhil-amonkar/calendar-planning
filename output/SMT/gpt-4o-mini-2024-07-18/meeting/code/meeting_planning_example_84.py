from z3 import *

# Initialize the Z3 solver
solver = Solver()

# Define the time variables
depart_haight = Real('depart_haight')  # Time you leave Alamo Square to head to Haight-Ashbury
arrive_haight = Real('arrive_haight')  # Time you arrive at Haight-Ashbury
depart_thomas = Real('depart_thomas')   # Time you leave Haight-Ashbury after meeting Thomas

# Constants
travel_time_alamo_to_haight = 5        # minutes from Alamo Square to Haight-Ashbury
travel_time_haight_to_alamo = 5         # minutes from Haight-Ashbury back to Alamo Square
meeting_duration = 30                    # minimum meeting duration (in minutes)
thomas_start = 11.0                     # 11:00 AM in hours
thomas_end = 13.0                       # 1:00 PM in hours
arrival_time_alamo = 9.0                 # 9:00 AM in hours

# Constraints
solver.add(arrive_haight == depart_haight + travel_time_alamo_to_haight)  # Arrival time at Haight-Ashbury
solver.add(depart_haight >= arrival_time_alamo)  # Must leave after arriving at Alamo Square
solver.add(depart_haight <= thomas_end - (meeting_duration / 60))  # Must leave in time to meet for 30 minutes
solver.add(arrive_haight >= thomas_start)  # Must arrive at or after Thomas starts being available
solver.add(depart_thomas >= arrive_haight + (meeting_duration / 60))  # Must leave after meeting for 30 minutes

# Maximize the meeting time with Thomas (ideally want to meet him for at least 30 minutes)
meet_time = min(depart_thomas - arrive_haight, meeting_duration / 60)

# We want to maximize the meeting time
solver.maximize(meet_time)

# Check if the solution is satisfiable and output the result
if solver.check() == sat:
    model = solver.model()
    depart_haight_val = model[depart_haight].as_decimal(2)
    arrive_haight_val = model[arrive_haight].as_decimal(2)
    depart_thomas_val = model[depart_thomas].as_decimal(2)

    print(f"Depart from Alamo Square to Haight-Ashbury at: {depart_haight_val} hours")
    print(f"Arrive at Haight-Ashbury at: {arrive_haight_val} hours")
    print(f"Depart from Haight-Ashbury after meeting Thomas at: {depart_thomas_val} hours")
else:
    print("No valid schedule found.")