from z3 import *

# Define the time in minutes from 9:00AM
def time_in_minutes(hour, minute):
    return (hour - 9) * 60 + minute

# Define the constraints
Richard_start = time_in_minutes(8, 45)
Richard_end = time_in_minutes(13, 0)
Charles_start = time_in_minutes(9, 45)
Charles_end = time_in_minutes(13, 0)

# Define the travel times in minutes
travel_times = {
    ('Bayview', 'Union Square'): 17,
    ('Bayview', 'Presidio'): 31,
    ('Union Square', 'Bayview'): 15,
    ('Union Square', 'Presidio'): 24,
    ('Presidio', 'Bayview'): 31,
    ('Presidio', 'Union Square'): 22
}

# Create the solver
solver = Solver()

# Define the variables for the start and end times of meetings
Richard_start_meeting = Int('Richard_start_meeting')
Richard_end_meeting = Int('Richard_end_meeting')
Charles_start_meeting = Int('Charles_start_meeting')
Charles_end_meeting = Int('Charles_end_meeting')

# Add constraints for Richard's meeting
solver.add(Richard_start_meeting >= Richard_start)
solver.add(Richard_end_meeting <= Richard_end)
solver.add(Richard_end_meeting - Richard_start_meeting >= 120)

# Add constraints for Charles's meeting
solver.add(Charles_start_meeting >= Charles_start)
solver.add(Charles_end_meeting <= Charles_end)
solver.add(Charles_end_meeting - Charles_start_meeting >= 120)

# Add constraints for travel times
# We assume we start at Bayview at 9:00AM (0 minutes)
start_time = 0

# Richard meeting after Bayview
solver.add(Richard_start_meeting >= start_time + travel_times[('Bayview', 'Union Square')])
solver.add(Richard_end_meeting <= Richard_start_meeting + (Richard_end - Richard_start))

# Charles meeting after Richard meeting
solver.add(Charles_start_meeting >= Richard_end_meeting + travel_times[('Union Square', 'Presidio')])
solver.add(Charles_end_meeting <= Charles_start_meeting + (Charles_end - Charles_start))

# Charles meeting after Bayview (if Richard meeting is skipped)
solver.add(Or(
    Charles_start_meeting >= start_time + travel_times[('Bayview', 'Presidio')],
    Charles_start_meeting >= Richard_end_meeting + travel_times[('Union Square', 'Presidio')]
))

# Check if the constraints are satisfiable
if solver.check() == sat:
    model = solver.model()
    Richard_start_meeting_time = model[Richard_start_meeting].as_long()
    Richard_end_meeting_time = model[Richard_end_meeting].as_long()
    Charles_start_meeting_time = model[Charles_start_meeting].as_long()
    Charles_end_meeting_time = model[Charles_end_meeting].as_long()

    def format_time(minutes):
        hours = 9 + minutes // 60
        minutes = minutes % 60
        return f"{hours:02}:{minutes:02}"

    itinerary = [
        {"action": "meet", "person": "Richard", "start_time": format_time(Richard_start_meeting_time), "end_time": format_time(Richard_end_meeting_time)},
        {"action": "meet", "person": "Charles", "start_time": format_time(Charles_start_meeting_time), "end_time": format_time(Charles_end_meeting_time)}
    ]

    print({"itinerary": itinerary})
else:
    print("No solution found")