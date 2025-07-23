from z3 import *

# Define the time in minutes since 9:00 AM
nine_am = 0
four_pm = 300  # 4:00 PM is 300 minutes after 9:00 AM
nine_pm = 645  # 9:45 PM is 645 minutes after 9:00 AM

# Define the travel time in minutes
travel_time = 23

# Create a solver instance
solver = Solver()

# Define the start and end time for meeting David
david_meeting_start = Int('david_meeting_start')
david_meeting_end = Int('david_meeting_end')

# Constraints
# David is available from 4:00 PM to 9:45 PM
solver.add(david_meeting_start >= four_pm)
solver.add(david_meeting_end <= nine_pm)

# The meeting with David should be exactly 105 minutes
solver.add(david_meeting_end - david_meeting_start == 105)

# The meeting should end before or at 9:45 PM
solver.add(david_meeting_end <= nine_pm)

# Check if the constraints are satisfiable
if solver.check() == sat:
    model = solver.model()
    start_time = model[david_meeting_start].as_long()
    end_time = model[david_meeting_end].as_long()

    # Convert time from minutes since 9:00 AM to HH:MM format
    def convert_to_time(minutes):
        hours = 9 + minutes // 60
        minutes = minutes % 60
        return f"{hours:02}:{minutes:02}"

    itinerary = [
        {"action": "meet", "person": "David", "start_time": convert_to_time(start_time), "end_time": convert_to_time(end_time)}
    ]

    print({"itinerary": itinerary})
else:
    print("No solution found")