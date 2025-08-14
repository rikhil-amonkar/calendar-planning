from z3 import *

# Define the time in minutes from 9:00AM
def time_in_minutes(hour, minute):
    return (hour - 9) * 60 + minute

# Define the travel times in minutes
travel_times = {
    ('Bayview', 'Union Square'): 17,
    ('Bayview', 'Presidio'): 31,
    ('Union Square', 'Bayview'): 15,
    ('Union Square', 'Presidio'): 24,
    ('Presidio', 'Bayview'): 31,
    ('Presidio', 'Union Square'): 22
}

# Define the availability of Richard and Charles in minutes from 9:00AM
richard_start = time_in_minutes(8, 45)
richard_end = time_in_minutes(13, 0)
charles_start = time_in_minutes(9, 45)
charles_end = time_in_minutes(13, 0)

# Define the minimum meeting duration in minutes
min_meeting_duration = 120

# Create the solver
solver = Solver()

# Define the start and end times for meetings with Richard and Charles
richard_meeting_start = Int('richard_meeting_start')
richard_meeting_end = Int('richard_meeting_end')
charles_meeting_start = Int('charles_meeting_start')
charles_meeting_end = Int('charles_meeting_end')

# Add constraints for Richard's meeting
solver.add(richard_meeting_start >= richard_start)
solver.add(richard_meeting_end <= richard_end)
solver.add(richard_meeting_end - richard_meeting_start >= min_meeting_duration)

# Add constraints for Charles's meeting
solver.add(charles_meeting_start >= charles_start)
solver.add(charles_meeting_end <= charles_end)
solver.add(charles_meeting_end - charles_meeting_start >= min_meeting_duration)

# Define the current location and time
current_location = 'Bayview'
current_time = 0  # 9:00AM

# Function to add travel constraints
def add_travel_constraints(start_location, end_location, start_time, end_time):
    travel_time = travel_times[(start_location, end_location)]
    solver.add(end_time - start_time >= travel_time)

# Add travel constraints for Richard's meeting
add_travel_constraints(current_location, 'Union Square', current_time, richard_meeting_start)

# Add travel constraints for Charles's meeting
add_travel_constraints('Union Square', 'Presidio', richard_meeting_end, charles_meeting_start)

# Check if the constraints are satisfiable
if solver.check() == sat:
    model = solver.model()
    richard_meeting_start_value = model[richard_meeting_start].as_long()
    richard_meeting_end_value = model[richard_meeting_end].as_long()
    charles_meeting_start_value = model[charles_meeting_start].as_long()
    charles_meeting_end_value = model[charles_meeting_end].as_long()

    # Convert the times back to HH:MM format
    def format_time(minutes):
        hours = 9 + minutes // 60
        minutes = minutes % 60
        return f"{hours:02}:{minutes:02}"

    itinerary = [
        {"action": "meet", "person": "Richard", "start_time": format_time(richard_meeting_start_value), "end_time": format_time(richard_meeting_end_value)},
        {"action": "meet", "person": "Charles", "start_time": format_time(charles_meeting_start_value), "end_time": format_time(charles_meeting_end_value)}
    ]

    print({"itinerary": itinerary})
else:
    print("No solution found")