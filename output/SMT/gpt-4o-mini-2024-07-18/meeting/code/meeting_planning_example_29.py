from z3 import *

# Initialize the Z3 solver
solver = Solver()

# Define the time variables
depart_haight = Real('depart_haight')  # Time we leave Sunset District to head to Haight-Ashbury
arrive_haight = Real('arrive_haight')  # Time we arrive at Haight-Ashbury
depart_nancy = Real('depart_nancy')     # Time we leave Haight-Ashbury after meeting with Nancy

# Constants
travel_time_sunset_to_haight = 15  # minutes
meeting_duration = 75                # minutes
nancy_start = 19.5                  # 7:30 PM in hours
nancy_end = 21.75                   # 9:45 PM in hours
arrival_time_sunset = 9.0           # 9:00 AM in hours

# Constraints
solver.add(arrive_haight == depart_haight + travel_time_sunset_to_haight)
solver.add(depart_haight >= arrival_time_sunset)  # Must leave after arriving at Sunset District
solver.add(depart_haight <= nancy_end - meeting_duration)  # Must leave in time to meet for 75 minutes
solver.add(arrive_haight >= nancy_start)  # Must arrive at or after Nancy starts being available
solver.add(depart_nancy >= arrive_haight + meeting_duration)  # Must leave after meeting for 75 minutes

# Maximize the meeting time with Nancy (ideally want to meet her for 75 minutes)
meet_time = min(depart_nancy - arrive_haight, meeting_duration)

# We want to maximize the meeting time
solver.maximize(meet_time)

# Check if the solution is satisfiable and output the result
if solver.check() == sat:
    model = solver.model()
    depart_haight_val = model[depart_haight].as_decimal(2)
    arrive_haight_val = model[arrive_haight].as_decimal(2)
    depart_nancy_val = model[depart_nancy].as_decimal(2)

    print(f"Depart from Sunset District to Haight-Ashbury at: {depart_haight_val} hours")
    print(f"Arrive at Haight-Ashbury at: {arrive_haight_val} hours")
    print(f"Depart from Haight-Ashbury after meeting Nancy at: {depart_nancy_val} hours")
else:
    print("No valid schedule found.")