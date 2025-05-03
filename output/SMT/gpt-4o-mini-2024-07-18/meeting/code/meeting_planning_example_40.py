from z3 import *

# Initialize the Z3 solver
solver = Solver()

# Define the time variables
depart_sunset = Real('depart_sunset')  # Time you leave The Castro to head to Sunset District
arrive_sunset = Real('arrive_sunset')  # Time you arrive at Sunset District
depart_deborah = Real('depart_deborah')  # Time you leave Sunset District after meeting Deborah

# Constants
travel_time_castro_to_sunset = 17  # minutes
meeting_duration = 75                # minutes
deborah_start = 14.25                # 2:15 PM in hours
deborah_end = 20.0                   # 8:00 PM in hours
arrival_time_castro = 9.0            # 9:00 AM in hours

# Constraints
solver.add(arrive_sunset == depart_sunset + travel_time_castro_to_sunset)
solver.add(depart_sunset >= arrival_time_castro)  # Must leave after arriving at The Castro
solver.add(depart_sunset <= deborah_end - meeting_duration)  # Must leave in time to meet for 75 minutes
solver.add(arrive_sunset >= deborah_start)  # Must arrive at or after Deborah starts being available
solver.add(depart_deborah >= arrive_sunset + meeting_duration)  # Must leave after meeting for 75 minutes

# Maximize the meeting time with Deborah (ideally want to meet her for 75 minutes)
meet_time = min(depart_deborah - arrive_sunset, meeting_duration)

# We want to maximize the meeting time
solver.maximize(meet_time)

# Check if the solution is satisfiable and output the result
if solver.check() == sat:
    model = solver.model()
    depart_sunset_val = model[depart_sunset].as_decimal(2)
    arrive_sunset_val = model[arrive_sunset].as_decimal(2)
    depart_deborah_val = model[depart_deborah].as_decimal(2)

    print(f"Depart from The Castro to Sunset District at: {depart_sunset_val} hours")
    print(f"Arrive at Sunset District at: {arrive_sunset_val} hours")
    print(f"Depart from Sunset District after meeting Deborah at: {depart_deborah_val} hours")
else:
    print("No valid schedule found.")