from z3 import *

# Define the time in minutes from 9:00AM
def time_in_minutes(hour, minute):
    return (hour - 9) * 60 + minute

# Define the travel times
travel_times = {
    ('Bayview', 'Nob Hill'): 20,
    ('Bayview', 'Union Square'): 17,
    ('Bayview', 'Chinatown'): 18,
    ('Bayview', 'The Castro'): 20,
    ('Bayview', 'Presidio'): 31,
    ('Bayview', 'Pacific Heights'): 23,
    ('Bayview', 'Russian Hill'): 23,
    ('Nob Hill', 'Bayview'): 19,
    ('Nob Hill', 'Union Square'): 7,
    ('Nob Hill', 'Chinatown'): 6,
    ('Nob Hill', 'The Castro'): 17,
    ('Nob Hill', 'Presidio'): 17,
    ('Nob Hill', 'Pacific Heights'): 8,
    ('Nob Hill', 'Russian Hill'): 5,
    ('Union Square', 'Bayview'): 15,
    ('Union Square', 'Nob Hill'): 9,
    ('Union Square', 'Chinatown'): 7,
    ('Union Square', 'The Castro'): 19,
    ('Union Square', 'Presidio'): 24,
    ('Union Square', 'Pacific Heights'): 15,
    ('Union Square', 'Russian Hill'): 13,
    ('Chinatown', 'Bayview'): 22,
    ('Chinatown', 'Nob Hill'): 8,
    ('Chinatown', 'Union Square'): 7,
    ('Chinatown', 'The Castro'): 22,
    ('Chinatown', 'Presidio'): 19,
    ('Chinatown', 'Pacific Heights'): 10,
    ('Chinatown', 'Russian Hill'): 7,
    ('The Castro', 'Bayview'): 19,
    ('The Castro', 'Nob Hill'): 16,
    ('The Castro', 'Union Square'): 19,
    ('The Castro', 'Chinatown'): 20,
    ('The Castro', 'Presidio'): 20,
    ('The Castro', 'Pacific Heights'): 16,
    ('The Castro', 'Russian Hill'): 18,
    ('Presidio', 'Bayview'): 31,
    ('Presidio', 'Nob Hill'): 18,
    ('Presidio', 'Union Square'): 22,
    ('Presidio', 'Chinatown'): 21,
    ('Presidio', 'The Castro'): 21,
    ('Presidio', 'Pacific Heights'): 11,
    ('Presidio', 'Russian Hill'): 14,
    ('Pacific Heights', 'Bayview'): 22,
    ('Pacific Heights', 'Nob Hill'): 8,
    ('Pacific Heights', 'Union Square'): 12,
    ('Pacific Heights', 'Chinatown'): 11,
    ('Pacific Heights', 'The Castro'): 16,
    ('Pacific Heights', 'Presidio'): 11,
    ('Pacific Heights', 'Russian Hill'): 7,
    ('Russian Hill', 'Bayview'): 23,
    ('Russian Hill', 'Nob Hill'): 5,
    ('Russian Hill', 'Union Square'): 11,
    ('Russian Hill', 'Chinatown'): 9,
    ('Russian Hill', 'The Castro'): 21,
    ('Russian Hill', 'Presidio'): 14,
    ('Russian Hill', 'Pacific Heights'): 7,
}

# Add travel times from a location to itself as 0
for loc in locations:
    travel_times[(loc, loc)] = 0

# Define the friends' availability
friends = {
    'Paul': (time_in_minutes(16, 15), time_in_minutes(21, 15), 60),
    'Carol': (time_in_minutes(18, 0), time_in_minutes(20, 15), 120),
    'Patricia': (time_in_minutes(20, 0), time_in_minutes(21, 30), 75),
    'Karen': (time_in_minutes(17, 0), time_in_minutes(19, 0), 45),
    'Nancy': (time_in_minutes(11, 45), time_in_minutes(22, 0), 30),
    'Jeffrey': (time_in_minutes(20, 0), time_in_minutes(20, 45), 45),
    'Matthew': (time_in_minutes(15, 45), time_in_minutes(21, 45), 75),
}

# Define the locations
locations = ['Bayview', 'Nob Hill', 'Union Square', 'Chinatown', 'The Castro', 'Presidio', 'Pacific Heights', 'Russian Hill']

# Create a solver
solver = Solver()

# Define the variables
current_location = 'Bayview'
current_time = 0
meetings = []

# Define the meeting variables
meeting_vars = {name: Int(name) for name in friends}
location_vars = {name: String(name + '_loc') for name in friends}

# Add constraints for each friend
for name, (start, end, duration) in friends.items():
    meeting_start = meeting_vars[name]
    solver.add(meeting_start >= start)
    solver.add(meeting_start + duration <= end)

# Add constraints for travel times
for i, (name, (start, end, duration)) in enumerate(friends.items()):
    if i == 0:
        prev_location = current_location
        prev_end_time = current_time
    else:
        prev_name, (prev_start, prev_end, prev_duration) = list(friends.items())[i-1]
        prev_location = location_vars[prev_name]
        prev_end_time = meeting_vars[prev_name] + prev_duration

    for loc in locations:
        travel_time = travel_times[(prev_location, loc)]
        meeting_start = meeting_vars[name]
        solver.add(Or(meeting_start >= prev_end_time + travel_time, meeting_start == prev_end_time + travel_time))

# Add constraints for location variables
for i, (name, (start, end, duration)) in enumerate(friends.items()):
    if i == 0:
        prev_location = current_location
    else:
        prev_name, (prev_start, prev_end, prev_duration) = list(friends.items())[i-1]
        prev_location = location_vars[prev_name]

    for loc in locations:
        meeting_start = meeting_vars[name]
        travel_time = travel_times[(prev_location, loc)]
        solver.add(Implies(meeting_start == prev_end_time + travel_time, location_vars[name] == loc))

# Check if the problem is solvable
if solver.check() == sat:
    model = solver.model()
    itinerary = []
    for name, (start, end, duration) in friends.items():
        meeting_start = model[meeting_vars[name]].as_long()
        meeting_end = meeting_start + duration
        meeting_location = model[location_vars[name]]
        itinerary.append({
            "action": "meet",
            "person": name,
            "start_time": f"{9 + meeting_start // 60:02}:{meeting_start % 60:02}",
            "end_time": f"{9 + meeting_end // 60:02}:{meeting_end % 60:02}",
            "location": meeting_location
        })
    itinerary.sort(key=lambda x: x["start_time"])
    print({"itinerary": itinerary})
else:
    print("No solution found")