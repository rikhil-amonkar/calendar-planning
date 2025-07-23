from z3 import *

# Define the time in minutes from 00:00
def time_in_minutes(hour, minute):
    return hour * 60 + minute

# Define the arrival time and Timothy's availability
arrival_time = time_in_minutes(9, 0)
timothy_start = time_in_minutes(20, 45)
timothy_end = time_in_minutes(21, 30)
timothy_min_meeting = 45

# Create a solver instance
solver = Solver()

# Define the start and end times for meeting Timothy
timothy_meeting_start = Int('timothy_meeting_start')
timothy_meeting_end = Int('timothy_meeting_end')

# Add constraints for meeting Timothy
solver.add(timothy_meeting_start >= arrival_time)
solver.add(timothy_meeting_start >= timothy_start)
solver.add(timothy_meeting_end <= timothy_end)
solver.add(timothy_meeting_end - timothy_meeting_start >= timothy_min_meeting)

# Check if the constraints are satisfiable
if solver.check() == sat:
    model = solver.model()
    timothy_meeting_start_value = model[timothy_meeting_start].as_long()
    timothy_meeting_end_value = model[timothy_meeting_end].as_long()
    
    # Convert back to HH:MM format
    def minutes_to_time(minutes):
        hours = minutes // 60
        minutes = minutes % 60
        return f"{hours:02}:{minutes:02}"
    
    itinerary = [
        {
            "action": "meet",
            "person": "Timothy",
            "start_time": minutes_to_time(timothy_meeting_start_value),
            "end_time": minutes_to_time(timothy_meeting_end_value)
        }
    ]
else:
    itinerary = []

SOLUTION = {"itinerary": itinerary}
print(SOLUTION)