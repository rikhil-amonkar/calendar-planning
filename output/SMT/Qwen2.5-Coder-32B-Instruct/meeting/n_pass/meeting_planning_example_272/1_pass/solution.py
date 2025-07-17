from z3 import *

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
current_location = String('current_location')
current_time = Int('current_time')
patricia_meeting_start = Int('patricia_meeting_start')
ashley_meeting_start = Int('ashley_meeting_start')
timothy_meeting_start = Int('timothy_meeting_start')

# Initial conditions
solver.add(current_location == 'Russian Hill')
solver.add(current_time == arrival_time)

# Constraints for meeting Patricia
solver.add(patricia_meeting_start >= patricia_start)
solver.add(patricia_meeting_start + patricia_duration <= patricia_end)

# Constraints for meeting Ashley
solver.add(ashley_meeting_start >= ashley_start)
solver.add(ashley_meeting_start + ashley_duration <= ashley_end)

# Constraints for meeting Timothy
solver.add(timothy_meeting_start >= timothy_start)
solver.add(timothy_meeting_start + timothy_duration <= timothy_end)

# Define the transitions
transitions = [
    (current_location == 'Russian Hill', current_time + travel_times[('Russian Hill', 'Nob Hill')], 'Nob Hill'),
    (current_location == 'Russian Hill', current_time + travel_times[('Russian Hill', 'Mission District')], 'Mission District'),
    (current_location == 'Russian Hill', current_time + travel_times[('Russian Hill', 'Embarcadero')], 'Embarcadero'),
    (current_location == 'Nob Hill', current_time + travel_times[('Nob Hill', 'Russian Hill')], 'Russian Hill'),
    (current_location == 'Nob Hill', current_time + travel_times[('Nob Hill', 'Mission District')], 'Mission District'),
    (current_location == 'Nob Hill', current_time + travel_times[('Nob Hill', 'Embarcadero')], 'Embarcadero'),
    (current_location == 'Mission District', current_time + travel_times[('Mission District', 'Russian Hill')], 'Russian Hill'),
    (current_location == 'Mission District', current_time + travel_times[('Mission District', 'Nob Hill')], 'Nob Hill'),
    (current_location == 'Mission District', current_time + travel_times[('Mission District', 'Embarcadero')], 'Embarcadero'),
    (current_location == 'Embarcadero', current_time + travel_times[('Embarcadero', 'Russian Hill')], 'Russian Hill'),
    (current_location == 'Embarcadero', current_time + travel_times[('Embarcadero', 'Nob Hill')], 'Nob Hill'),
    (current_location == 'Embarcadero', current_time + travel_times[('Embarcadero', 'Mission District')], 'Mission District'),
]

# Add transitions to the solver
for condition, new_time, new_location in transitions:
    solver.add(Implies(condition, And(current_time == new_time, current_location == new_location)))

# Check if the problem is solvable
if solver.check() == sat:
    model = solver.model()
    itinerary = []

    # Add meetings to the itinerary
    if model.evaluate(patricia_meeting_start).as_long() >= patricia_start:
        itinerary.append({
            "action": "meet",
            "person": "Patricia",
            "start_time": minutes_to_time(model.evaluate(patricia_meeting_start).as_long()),
            "end_time": minutes_to_time(model.evaluate(patricia_meeting_start).as_long() + patricia_duration)
        })

    if model.evaluate(ashley_meeting_start).as_long() >= ashley_start:
        itinerary.append({
            "action": "meet",
            "person": "Ashley",
            "start_time": minutes_to_time(model.evaluate(ashley_meeting_start).as_long()),
            "end_time": minutes_to_time(model.evaluate(ashley_meeting_start).as_long() + ashley_duration)
        })

    if model.evaluate(timothy_meeting_start).as_long() >= timothy_start:
        itinerary.append({
            "action": "meet",
            "person": "Timothy",
            "start_time": minutes_to_time(model.evaluate(timothy_meeting_start).as_long()),
            "end_time": minutes_to_time(model.evaluate(timothy_meeting_start).as_long() + timothy_duration)
        })

    # Sort the itinerary by start time
    itinerary.sort(key=lambda x: time_to_minutes(x['start_time']))

    # Print the solution
    print(f"SOLUTION: {json.dumps({'itinerary': itinerary})}")
else:
    print("No solution found")