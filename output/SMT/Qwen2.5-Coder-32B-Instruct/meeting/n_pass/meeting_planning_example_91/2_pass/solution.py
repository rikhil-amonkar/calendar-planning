from z3 import *

# Define the time in minutes from 00:00
def time_in_minutes(hour, minute):
    return hour * 60 + minute

# Define the start and end times for Daniel's availability
daniel_start = time_in_minutes(19, 0)  # 7:00 PM
daniel_end = time_in_minutes(20, 15)    # 8:15 PM

# Define the travel times
travel_russian_to_richmond = 14
travel_richmond_to_russian = 13

# Define the solver
solver = Solver()

# Define the variables for the meeting start and end times
meet_start = Int('meet_start')
meet_end = Int('meet_end')

# Constraints
# Meeting must be within Daniel's availability
solver.add(meet_start >= daniel_start)
solver.add(meet_end <= daniel_end)

# Meeting must be at least 75 minutes
solver.add(meet_end - meet_start >= 75)

# Meeting must start after arrival and account for travel time
arrival_time = time_in_minutes(9, 0)  # 9:00 AM
solver.add(meet_start >= arrival_time + travel_russian_to_richmond)

# Meeting must end before leaving Richmond District and account for travel time
solver.add(meet_end + travel_richmond_to_russian <= daniel_end)

# Check if the constraints are satisfiable
if solver.check() == sat:
    model = solver.model()
    meet_start_value = model[meet_start].as_long()
    meet_end_value = model[meet_end].as_long()

    # Convert the meeting times back to HH:MM format
    def format_time(minutes):
        hours = minutes // 60
        minutes = minutes % 60
        return f"{hours:02}:{minutes:02}"

    itinerary = [
        {
            "action": "meet",
            "person": "Daniel",
            "start_time": format_time(meet_start_value),
            "end_time": format_time(meet_end_value)
        }
    ]

    print({"itinerary": itinerary})
else:
    print("No feasible schedule found.")