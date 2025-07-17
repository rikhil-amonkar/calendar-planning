from z3 import *

# Define the time in minutes from 9:00AM
def time_in_minutes(hour, minute):
    return (hour - 9) * 60 + minute

# Define the travel times in minutes
travel_times = {
    ('North Beach', 'Union Square'): 7,
    ('North Beach', 'Russian Hill'): 4,
    ('Union Square', 'North Beach'): 10,
    ('Union Square', 'Russian Hill'): 13,
    ('Russian Hill', 'North Beach'): 5,
    ('Russian Hill', 'Union Square'): 11
}

# Define the constraints for Emily and Margaret
emily_start = time_in_minutes(16, 0)  # 4:00PM
emily_end = time_in_minutes(17, 15)   # 5:15PM
emily_min_meeting = 45

margaret_start = time_in_minutes(19, 0)  # 7:00PM
margaret_end = time_in_minutes(21, 0)    # 9:00PM
margaret_min_meeting = 120

# Create a solver instance
solver = Solver()

# Define the variables for the start and end times of meetings
emily_start_time = Int('emily_start_time')
emily_end_time = Int('emily_end_time')
margaret_start_time = Int('margaret_start_time')
margaret_end_time = Int('margaret_end_time')

# Add constraints for Emily
solver.add(emily_start_time >= emily_start)
solver.add(emily_end_time <= emily_end)
solver.add(emily_end_time - emily_start_time >= emily_min_meeting)

# Add constraints for Margaret
solver.add(margaret_start_time >= margaret_start)
solver.add(margaret_end_time <= margaret_end)
solver.add(margaret_end_time - margaret_start_time >= margaret_min_meeting)

# Define the current location and time
current_location = 'North Beach'
current_time = 0  # 9:00AM

# Function to add travel constraints
def add_travel_constraints(start_location, end_location, start_time, end_time):
    travel_time = travel_times[(start_location, end_location)]
    solver.add(end_time == start_time + travel_time)

# Add travel constraints for Emily
emily_travel_time = travel_times[(current_location, 'Union Square')]
solver.add(emily_start_time == current_time + emily_travel_time)

# Add travel constraints for Margaret
margaret_travel_time = travel_times[('Union Square', 'Russian Hill')]
solver.add(margaret_start_time == emily_end_time + margaret_travel_time)

# Check if the constraints are satisfiable
if solver.check() == sat:
    model = solver.model()
    emily_start_time_value = model[emily_start_time].as_long()
    emily_end_time_value = model[emily_end_time].as_long()
    margaret_start_time_value = model[margaret_start_time].as_long()
    margaret_end_time_value = model[margaret_end_time].as_long()

    # Convert times back to HH:MM format
    def time_to_string(minutes):
        hours = minutes // 60 + 9
        minutes = minutes % 60
        return f"{hours:02}:{minutes:02}"

    itinerary = [
        {"action": "meet", "person": "Emily", "start_time": time_to_string(emily_start_time_value), "end_time": time_to_string(emily_end_time_value)},
        {"action": "meet", "person": "Margaret", "start_time": time_to_string(margaret_start_time_value), "end_time": time_to_string(margaret_end_time_value)}
    ]

    print({"itinerary": itinerary})
else:
    print("No feasible schedule found")