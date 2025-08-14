from z3 import *

# Define the time in minutes from 9:00AM
def time_in_minutes(hour, minute):
    return (hour - 9) * 60 + minute

# Define the travel times in minutes
travel_times = {
    ('The Castro', 'Mission District'): 7,
    ('The Castro', 'Financial District'): 20,
    ('Mission District', 'The Castro'): 7,
    ('Mission District', 'Financial District'): 17,
    ('Financial District', 'The Castro'): 23,
    ('Financial District', 'Mission District'): 17
}

# Define the availability of friends
laura_availability = (time_in_minutes(12, 15), time_in_minutes(19, 45))
anthony_availability = (time_in_minutes(12, 30), time_in_minutes(14, 45))

# Define the minimum meeting durations in minutes
laura_min_meeting = 75
anthony_min_meeting = 30

# Create a solver instance
solver = Solver()

# Define the start and end times for meetings with Laura and Anthony
laura_start = Int('laura_start')
laura_end = Int('laura_end')
anthony_start = Int('anthony_start')
anthony_end = Int('anthony_end')

# Add constraints for Laura's meeting
solver.add(laura_start >= laura_availability[0])
solver.add(laura_end <= laura_availability[1])
solver.add(laura_end - laura_start >= laura_min_meeting)

# Add constraints for Anthony's meeting
solver.add(anthony_start >= anthony_availability[0])
solver.add(anthony_end <= anthony_availability[1])
solver.add(anthony_end - anthony_start >= anthony_min_meeting)

# Define the current location and time
current_location = 'The Castro'
current_time = 0  # 9:00AM

# Define the travel constraints
if current_location == 'The Castro':
    solver.add(laura_start >= current_time + travel_times[('The Castro', 'Mission District')])
    solver.add(anthony_start >= current_time + travel_times[('The Castro', 'Financial District')])

# Define the end time of the last meeting
last_meeting_end = Int('last_meeting_end')
solver.add(last_meeting_end == If(laura_end > anthony_end, laura_end, anthony_end))

# Define the objective to maximize the number of meetings
# Since we have only two meetings, we just need to ensure both are possible
objective = And(laura_start >= 0, laura_end >= 0, anthony_start >= 0, anthony_end >= 0)

# Check if the constraints are satisfiable
if solver.check(objective) == sat:
    model = solver.model()
    laura_start_time = model[laura_start].as_long()
    laura_end_time = model[laura_end].as_long()
    anthony_start_time = model[anthony_start].as_long()
    anthony_end_time = model[anthony_end].as_long()

    # Convert times back to HH:MM format
    def format_time(minutes):
        hours = minutes // 60 + 9
        minutes = minutes % 60
        return f"{hours:02}:{minutes:02}"

    itinerary = [
        {"action": "meet", "person": "Laura", "start_time": format_time(laura_start_time), "end_time": format_time(laura_end_time)},
        {"action": "meet", "person": "Anthony", "start_time": format_time(anthony_start_time), "end_time": format_time(anthony_end_time)}
    ]

    # Sort the itinerary by start time
    itinerary.sort(key=lambda x: x['start_time'])

    # Print the solution in JSON format
    solution = {"itinerary": itinerary}
    print(solution)
else:
    print("No solution found")