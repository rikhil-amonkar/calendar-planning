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
# We need to define a sequence of actions that respects the time constraints and travel times
# Let's assume we can only make one transition per hour for simplicity
max_time = time_to_minutes("23:59")
time_step = 60  # One hour time steps

# Define the sequence of actions
actions = []
for t in range(arrival_time, max_time, time_step):
    actions.append((Int(f'action_{t}'), Int(f'time_{t}'), String(f'location_{t}')))

# Initial action
solver.add(actions[0][0] == 0)  # No action at the start
solver.add(actions[0][1] == arrival_time)
solver.add(actions[0][2] == 'Russian Hill')

# Define the transitions
for i in range(len(actions) - 1):
    action, time, location = actions[i]
    next_action, next_time, next_location = actions[i + 1]
    
    # No action
    solver.add(Implies(action == 0, And(next_time == time, next_location == location)))
    
    # Transition to Nob Hill
    solver.add(Implies(action == 1, And(next_time == time + travel_times[(location, 'Nob Hill')], next_location == 'Nob Hill')))
    
    # Transition to Mission District
    solver.add(Implies(action == 2, And(next_time == time + travel_times[(location, 'Mission District')], next_location == 'Mission District')))
    
    # Transition to Embarcadero
    solver.add(Implies(action == 3, And(next_time == time + travel_times[(location, 'Embarcadero')], next_location == 'Embarcadero')))
    
    # Meeting Patricia
    solver.add(Implies(action == 4, And(next_time == time + patricia_duration, next_location == 'Nob Hill')))
    
    # Meeting Ashley
    solver.add(Implies(action == 5, And(next_time == time + ashley_duration, next_location == 'Mission District')))
    
    # Meeting Timothy
    solver.add(Implies(action == 6, And(next_time == time + timothy_duration, next_location == 'Embarcadero')))

# Ensure we meet Patricia
solver.add(Or([And(action == 4, time >= patricia_start, time + patricia_duration <= patricia_end) for action, time, location in actions]))

# Ensure we meet Ashley
solver.add(Or([And(action == 5, time >= ashley_start, time + ashley_duration <= ashley_end) for action, time, location in actions]))

# Ensure we meet Timothy
solver.add(Or([And(action == 6, time >= timothy_start, time + timothy_duration <= timothy_end) for action, time, location in actions]))

# Check if the problem is solvable
if solver.check() == sat:
    model = solver.model()
    itinerary = []

    # Extract the itinerary from the model
    for action, time, location in actions:
        action_val = model.evaluate(action).as_long()
        time_val = model.evaluate(time).as_long()
        location_val = model.evaluate(location).as_string()[1:-1]
        
        if action_val == 4:
            itinerary.append({
                "action": "meet",
                "person": "Patricia",
                "start_time": minutes_to_time(time_val),
                "end_time": minutes_to_time(time_val + patricia_duration)
            })
        elif action_val == 5:
            itinerary.append({
                "action": "meet",
                "person": "Ashley",
                "start_time": minutes_to_time(time_val),
                "end_time": minutes_to_time(time_val + ashley_duration)
            })
        elif action_val == 6:
            itinerary.append({
                "action": "meet",
                "person": "Timothy",
                "start_time": minutes_to_time(time_val),
                "end_time": minutes_to_time(time_val + timothy_duration)
            })

    # Sort the itinerary by start time
    itinerary.sort(key=lambda x: time_to_minutes(x['start_time']))

    # Print the solution
    print(f"SOLUTION: {json.dumps({'itinerary': itinerary})}")
else:
    print("No solution found")