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

# Define the availability of Emily and Margaret
emily_start = time_in_minutes(16, 0)  # 4:00PM
emily_end = time_in_minutes(17, 15)   # 5:15PM
margaret_start = time_in_minutes(19, 0)  # 7:00PM
margaret_end = time_in_minutes(21, 0)   # 9:00PM

# Define the minimum meeting durations
emily_min_duration = 45
margaret_min_duration = 120

# Define the solver
solver = Solver()

# Define the variables for the start and end times of meetings
emily_start_time = Int('emily_start_time')
emily_end_time = Int('emily_end_time')
margaret_start_time = Int('margaret_start_time')
margaret_end_time = Int('margaret_end_time')

# Define the constraints
solver.add(emily_start_time >= emily_start)
solver.add(emily_end_time <= emily_end)
solver.add(emily_end_time - emily_start_time >= emily_min_duration)

solver.add(margaret_start_time >= margaret_start)
solver.add(margaret_end_time <= margaret_end)
solver.add(margaret_end_time - margaret_start_time >= margaret_min_duration)

# Define the travel constraints
# We need to ensure that the travel time between meetings is respected
# Since we start at North Beach at 9:00AM, we need to account for travel time to Union Square for Emily
# and to Russian Hill for Margaret

# Emily meeting constraints
solver.add(emily_start_time >= travel_times[('North Beach', 'Union Square')])

# Margaret meeting constraints
solver.add(margaret_start_time >= emily_end_time + travel_times[('Union Square', 'Russian Hill')])

# Check if the constraints are satisfiable
if solver.check() == sat:
    model = solver.model()
    emily_start_time_value = model[emily_start_time].as_long()
    emily_end_time_value = model[emily_end_time].as_long()
    margaret_start_time_value = model[margaret_start_time].as_long()
    margaret_end_time_value = model[margaret_end_time].as_long()

    # Convert the times back to HH:MM format
    def format_time(minutes):
        hours = 9 + minutes // 60
        minutes = minutes % 60
        return f"{hours:02}:{minutes:02}"

    itinerary = [
        {"action": "meet", "person": "Emily", "start_time": format_time(emily_start_time_value), "end_time": format_time(emily_end_time_value)},
        {"action": "meet", "person": "Margaret", "start_time": format_time(margaret_start_time_value), "end_time": format_time(margaret_end_time_value)}
    ]

    print({"itinerary": itinerary})
else:
    print("No solution found")