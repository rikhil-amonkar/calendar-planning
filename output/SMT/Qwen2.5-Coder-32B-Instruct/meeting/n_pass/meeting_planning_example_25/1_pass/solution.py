from z3 import *

# Define the time in minutes since 00:00
nine_am = 9 * 60
four_pm = 16 * 60
nine_pm = 21 * 60
travel_time = 23  # in minutes

# Create a solver instance
solver = Solver()

# Define the start and end time for meeting David as integer variables
david_meeting_start = Int('david_meeting_start')
david_meeting_end = Int('david_meeting_end')

# Add constraints
# David is available from 4:00PM to 9:45PM
solver.add(david_meeting_start >= four_pm)
solver.add(david_meeting_end <= nine_pm + 45)  # 9:45PM in minutes

# The meeting with David should be at least 105 minutes
solver.add(david_meeting_end - david_meeting_start >= 105)

# The meeting should start after arriving at Golden Gate Park at 9:00AM
solver.add(david_meeting_start >= nine_am + travel_time)  # Account for travel time

# Optimize to maximize the meeting duration with David
objective = Optimize()
objective.add(solver.assertions())
objective.maximize(david_meeting_end - david_meeting_start)

# Check if the problem is solvable
if objective.check() == sat:
    model = objective.model()
    start_time = model[david_meeting_start].as_long()
    end_time = model[david_meeting_end].as_long()
    
    # Convert time from minutes since 00:00 to HH:MM format
    def format_time(minutes):
        hours = minutes // 60
        minutes = minutes % 60
        return f"{hours:02}:{minutes:02}"
    
    itinerary = [
        {"action": "meet", "person": "David", "start_time": format_time(start_time), "end_time": format_time(end_time)}
    ]
    
    print({"itinerary": itinerary})
else:
    print("No solution found")