from z3 import *

# Define the time in minutes since 00:00
def time_to_minutes(time_str):
    hours, minutes = map(int, time_str.split(':'))
    return hours * 60 + minutes

def minutes_to_time(minutes):
    hours = minutes // 60
    minutes = minutes % 60
    return f"{hours:02}:{minutes:02}"

# Define the arrival time and Daniel's availability
arrival_time = time_to_minutes("09:00")
daniel_start = time_to_minutes("19:00")
daniel_end = time_to_minutes("20:15")
min_meeting_duration = 75

# Create a solver instance
solver = Solver()

# Define the start and end time of the meeting with Daniel as variables
daniel_meeting_start = Int('daniel_meeting_start')
daniel_meeting_end = Int('daniel_meeting_end')

# Add constraints
solver.add(daniel_meeting_start >= arrival_time)  # Start after arrival
solver.add(daniel_meeting_start >= daniel_start)  # Start within Daniel's availability
solver.add(daniel_meeting_end <= daniel_end)      # End within Daniel's availability
solver.add(daniel_meeting_end - daniel_meeting_start >= min_meeting_duration)  # Minimum meeting duration

# Check if the constraints are satisfiable
if solver.check() == sat:
    model = solver.model()
    daniel_meeting_start_minutes = model[daniel_meeting_start].as_long()
    daniel_meeting_end_minutes = model[daniel_meeting_end].as_long()
    itinerary = [
        {
            "action": "meet",
            "person": "Daniel",
            "start_time": minutes_to_time(daniel_meeting_start_minutes),
            "end_time": minutes_to_time(daniel_meeting_end_minutes)
        }
    ]
else:
    itinerary = []

# Output the solution in JSON format
solution = {"itinerary": itinerary}
print(solution)