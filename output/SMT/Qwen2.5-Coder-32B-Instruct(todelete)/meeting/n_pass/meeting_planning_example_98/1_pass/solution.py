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

# Define the decision variables for meeting Timothy
meet_timothy_start = Int('meet_timothy_start')
meet_timothy_end = Int('meet_timothy_end')

# Add constraints for meeting Timothy
solver.add(meet_timothy_start >= arrival_time)
solver.add(meet_timothy_end <= timothy_end)
solver.add(meet_timothy_end - meet_timothy_start >= timothy_min_meeting)
solver.add(meet_timothy_start >= timothy_start)

# Check if the constraints are satisfiable
if solver.check() == sat:
    model = solver.model()
    meet_timothy_start_value = model[meet_timothy_start].as_long()
    meet_timothy_end_value = model[meet_timothy_end].as_long()
    
    # Convert the meeting times back to HH:MM format
    def format_time(minutes):
        hours = minutes // 60
        minutes = minutes % 60
        return f"{hours:02}:{minutes:02}"
    
    itinerary = [
        {
            "action": "meet",
            "person": "Timothy",
            "start_time": format_time(meet_timothy_start_value),
            "end_time": format_time(meet_timothy_end_value)
        }
    ]
else:
    itinerary = []

# Output the result as a JSON-formatted dictionary
result = {"itinerary": itinerary}
print(result)