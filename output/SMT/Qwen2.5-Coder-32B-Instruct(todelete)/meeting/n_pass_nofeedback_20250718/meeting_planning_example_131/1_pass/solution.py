from z3 import *

# Define the time in minutes from 9:00AM
def time_in_minutes(hour, minute):
    return (hour - 9) * 60 + minute

# Define the travel times in minutes
travel_times = {
    ('Pacific Heights', 'Presidio'): 11,
    ('Pacific Heights', 'Marina District'): 6,
    ('Presidio', 'Pacific Heights'): 11,
    ('Presidio', 'Marina District'): 10,
    ('Marina District', 'Pacific Heights'): 7,
    ('Marina District', 'Presidio'): 10
}

# Define the availability of Jason and Kenneth
jason_start = time_in_minutes(10, 0)
jason_end = time_in_minutes(16, 15)
kenneth_start = time_in_minutes(15, 30)
kenneth_end = time_in_minutes(16, 45)

# Define the minimum meeting durations
jason_min_duration = 90
kenneth_min_duration = 45

# Create the solver
solver = Solver()

# Define the decision variables for the start and end times of meetings
jason_start_meeting = Int('jason_start_meeting')
jason_end_meeting = Int('jason_end_meeting')
kenneth_start_meeting = Int('kenneth_start_meeting')
kenneth_end_meeting = Int('kenneth_end_meeting')

# Add constraints for Jason's meeting
solver.add(jason_start_meeting >= jason_start)
solver.add(jason_end_meeting <= jason_end)
solver.add(jason_end_meeting - jason_start_meeting >= jason_min_duration)

# Add constraints for Kenneth's meeting
solver.add(kenneth_start_meeting >= kenneth_start)
solver.add(kenneth_end_meeting <= kenneth_end)
solver.add(kenneth_end_meeting - kenneth_start_meeting >= kenneth_min_duration)

# Define the decision variables for the travel times
travel_jason_to_kenneth = Int('travel_jason_to_kenneth')
travel_kenneth_to_jason = Int('travel_kenneth_to_jason')

# Add constraints for travel times
solver.add(travel_jason_to_kenneth == travel_times[('Presidio', 'Marina District')])
solver.add(travel_kenneth_to_jason == travel_times[('Marina District', 'Presidio')])

# Ensure that the meetings do not overlap and that there is enough time to travel between them
solver.add(jason_end_meeting + travel_jason_to_kenneth <= kenneth_start_meeting)
solver.add(kenneth_end_meeting + travel_kenneth_to_jason <= jason_start_meeting)

# Check if the constraints are satisfiable
if solver.check() == sat:
    model = solver.model()
    jason_start_meeting_value = model[jason_start_meeting].as_long()
    jason_end_meeting_value = model[jason_end_meeting].as_long()
    kenneth_start_meeting_value = model[kenneth_start_meeting].as_long()
    kenneth_end_meeting_value = model[kenneth_end_meeting].as_long()

    # Convert the times back to HH:MM format
    def format_time(minutes):
        hours = 9 + minutes // 60
        minutes = minutes % 60
        return f"{hours:02}:{minutes:02}"

    itinerary = [
        {"action": "meet", "person": "Jason", "start_time": format_time(jason_start_meeting_value), "end_time": format_time(jason_end_meeting_value)},
        {"action": "meet", "person": "Kenneth", "start_time": format_time(kenneth_start_meeting_value), "end_time": format_time(kenneth_end_meeting_value)}
    ]

    print({"itinerary": itinerary})
else:
    print("No solution found")