from z3 import *
import json

# Define the time in minutes from 00:00 to 23:59
def time_to_minutes(time_str):
    hours, minutes = map(int, time_str.split(':'))
    return hours * 60 + minutes

def minutes_to_time(minutes):
    hours = minutes // 60
    minutes = minutes % 60
    return f"{hours:02}:{minutes:02}"

# Define the travel times
travel_times = {
    ('Russian Hill', 'Nob Hill'): 5,
    ('Russian Hill', 'Mission District'): 16,
    ('Russian Hill', 'Embarcadero'): 8,
    ('Nob Hill', 'Russian Hill'): 5,
    ('Nob Hill', 'Mission District'): 13,
    ('Nob Hill', 'Embarcadero'): 9,
    ('Mission District', 'Russian Hill'): 15,
    ('Mission District', 'Nob Hill'): 12,
    ('Mission District', 'Embarcadero'): 19,
    ('Embarcadero', 'Russian Hill'): 8,
    ('Embarcadero', 'Nob Hill'): 10,
    ('Embarcadero', 'Mission District'): 20,
}

# Define the constraints
arrival_time = time_to_minutes("09:00")
patricia_start = time_to_minutes("18:30")
patricia_end = time_to_minutes("21:45")
ashley_start = time_to_minutes("20:30")
ashley_end = time_to_minutes("21:15")
timothy_start = time_to_minutes("09:45")
timothy_end = time_to_minutes("17:45")

# Define the meeting durations
patricia_duration = 90
ashley_duration = 45
timothy_duration = 120

# Define the locations
locations = ['Russian Hill', 'Nob Hill', 'Mission District', 'Embarcadero']

# Create the solver
solver = Solver()

# Define the variables
current_time = Int('current_time')
timothy_meeting_start = Int('timothy_meeting_start')
ashley_meeting_start = Int('ashley_meeting_start')
patricia_meeting_start = Int('patricia_meeting_start')

# Initial conditions
solver.add(current_time == arrival_time)

# Define the meeting constraints
solver.add(timothy_meeting_start >= timothy_start)
solver.add(timothy_meeting_start + timothy_duration <= timothy_end)

solver.add(patricia_meeting_start >= patricia_start)
solver.add(patricia_meeting_start + patricia_duration <= patricia_end)

solver.add(ashley_meeting_start >= ashley_start)
solver.add(ashley_meeting_start + ashley_duration <= ashley_end)

# Define the travel constraints
# Travel to Timothy
timothy_travel_time = Int('timothy_travel_time')
solver.add(timothy_travel_time == travel_times[('Russian Hill', 'Embarcadero')])
solver.add(timothy_meeting_start >= current_time + timothy_travel_time)

# Travel to Patricia
patricia_travel_time = Int('patricia_travel_time')
solver.add(patricia_travel_time == travel_times[('Embarcadero', 'Nob Hill')])
solver.add(patricia_meeting_start >= timothy_meeting_start + timothy_duration + patricia_travel_time)

# Travel to Ashley
ashley_travel_time = Int('ashley_travel_time')
solver.add(ashley_travel_time == travel_times[('Nob Hill', 'Mission District')])
solver.add(ashley_meeting_start >= patricia_meeting_start + patricia_duration + ashley_travel_time)

# Check if the problem is solvable
if solver.check() == sat:
    model = solver.model()
    itinerary = [
        {"action": "meet", "person": "Timothy", "start_time": minutes_to_time(model[timothy_meeting_start].as_long()), "end_time": minutes_to_time(model[timothy_meeting_start].as_long() + timothy_duration)},
        {"action": "meet", "person": "Patricia", "start_time": minutes_to_time(model[patricia_meeting_start].as_long()), "end_time": minutes_to_time(model[patricia_meeting_start].as_long() + patricia_duration)},
        {"action": "meet", "person": "Ashley", "start_time": minutes_to_time(model[ashley_meeting_start].as_long()), "end_time": minutes_to_time(model[ashley_meeting_start].as_long() + ashley_duration)},
    ]
    print(f"SOLUTION: {json.dumps({'itinerary': itinerary})}")
else:
    print("No solution found")