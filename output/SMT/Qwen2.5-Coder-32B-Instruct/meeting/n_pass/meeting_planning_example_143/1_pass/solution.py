from z3 import *

# Define the time in minutes from 9:00AM
def time_in_minutes(hour, minute):
    return (hour - 9) * 60 + minute

# Define the travel times in minutes
travel_times = {
    ('North Beach', 'Pacific Heights'): 8,
    ('North Beach', 'Embarcadero'): 6,
    ('Pacific Heights', 'North Beach'): 9,
    ('Pacific Heights', 'Embarcadero'): 10,
    ('Embarcadero', 'North Beach'): 5,
    ('Embarcadero', 'Pacific Heights'): 11
}

# Define the availability of friends
karen_start = time_in_minutes(18, 45)  # 6:45PM
karen_end = time_in_minutes(20, 15)    # 8:15PM
mark_start = time_in_minutes(13, 0)    # 1:00PM
mark_end = time_in_minutes(17, 45)     # 5:45PM

# Define the minimum meeting durations in minutes
karen_min_duration = 90
mark_min_duration = 120

# Define the solver
solver = Solver()

# Define the variables for the start and end times of meetings
karen_start_meeting = Int('karen_start_meeting')
karen_end_meeting = Int('karen_end_meeting')
mark_start_meeting = Int('mark_start_meeting')
mark_end_meeting = Int('mark_end_meeting')

# Define the constraints
solver.add(karen_start_meeting >= karen_start)
solver.add(karen_end_meeting <= karen_end)
solver.add(karen_end_meeting - karen_start_meeting >= karen_min_duration)

solver.add(mark_start_meeting >= mark_start)
solver.add(mark_end_meeting <= mark_end)
solver.add(mark_end_meeting - mark_start_meeting >= mark_min_duration)

# Define the travel constraints
# Assume we start at North Beach at 9:00AM (0 minutes)
current_location = 'North Beach'
current_time = 0

# Travel to Mark's location
solver.add(mark_start_meeting >= current_time + travel_times[(current_location, 'Embarcadero')])

# Travel from Mark's location to Karen's location
solver.add(karen_start_meeting >= mark_end_meeting + travel_times[('Embarcadero', 'Pacific Heights')])

# Check if the problem is solvable
if solver.check() == sat:
    model = solver.model()
    karen_start_meeting_time = model[karen_start_meeting].as_long()
    karen_end_meeting_time = model[karen_end_meeting].as_long()
    mark_start_meeting_time = model[mark_start_meeting].as_long()
    mark_end_meeting_time = model[mark_end_meeting].as_long()

    def format_time(minutes):
        hours = 9 + minutes // 60
        minutes = minutes % 60
        return f"{hours:02}:{minutes:02}"

    itinerary = [
        {"action": "meet", "person": "Mark", "start_time": format_time(mark_start_meeting_time), "end_time": format_time(mark_end_meeting_time)},
        {"action": "meet", "person": "Karen", "start_time": format_time(karen_start_meeting_time), "end_time": format_time(karen_end_meeting_time)}
    ]

    print({"itinerary": itinerary})
else:
    print("No solution found")