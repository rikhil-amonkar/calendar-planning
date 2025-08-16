from z3 import *

# Define friends and their data
friends = [
    {
        'name': 'Mary',
        'location': 'Embarcadero',
        'available_start': 20 * 60,  # 8 PM
        'available_end': 21 * 60 + 15,  # 9:15 PM
        'required_duration': 75
    },
    {
        'name': 'Kenneth',
        'location': 'The Castro',
        'available_start': 11 * 60 + 15,  # 11:15 AM
        'available_end': 19 * 60,  # 7 PM
        'required_duration': 30
    },
    {
        'name': 'Joseph',
        'location': 'Haight-Ashbury',
        'available_start': 20 * 60,  # 8 PM
        'available_end': 22 * 60,  # 10 PM
        'required_duration': 120
    },
    {
        'name': 'Sarah',
        'location': 'Union Square',
        'available_start': 11 * 60 + 45,  # 11:45 AM
        'available_end': 14 * 60 + 30,  # 2:30 PM
        'required_duration': 90
    },
    {
        'name': 'Thomas',
        'location': 'North Beach',
        'available_start': 19 * 60 + 15,  # 7:15 PM
        'available_end': 19 * 60 + 45,  # 7:45 PM
        'required_duration': 15
    },
    {
        'name': 'Daniel',
        'location': 'Pacific Heights',
        'available_start': 13 * 60 + 45,  # 1:45 PM
        'available_end': 20 * 60 + 30,  # 8:30 PM
        'required_duration': 15
    },
    {
        'name': 'Richard',
        'location': 'Chinatown',
        'available_start': 8 * 60,  # 8 AM
        'available_end': 18 * 60 + 45,  # 6:45 PM
        'required_duration': 30
    },
    {
        'name': 'Mark',
        'location': 'Golden Gate Park',
        'available_start': 17 * 60 + 30,  # 5:30 PM
        'available_end': 21 * 60 + 30,  # 9:30 PM
        'required_duration': 120
    },
    {
        'name': 'David',
        'location': 'Marina District',
        'available_start': 20 * 60,  # 8 PM
        'available_end': 21 * 60,  # 9 PM
        'required_duration': 60
    },
    {
        'name': 'Karen',
        'location': 'Russian Hill',
        'available_start': 13 * 60 + 15,  # 1:15 PM
        'available_end': 18 * 60 + 30,  # 6:30 PM
        'required_duration': 120
    },
]

# Define travel times between locations
travel_time = {
    # From Nob Hill
    ('Nob Hill', 'Embarcadero'): 9,
    ('Nob Hill', 'The Castro'): 17,
    ('Nob Hill', 'Haight-Ashbury'): 13,
    ('Nob Hill', 'Union Square'): 7,
    ('Nob Hill', 'North Beach'): 8,
    ('Nob Hill', 'Pacific Heights'): 8,
    ('Nob Hill', 'Chinatown'): 6,
    ('Nob Hill', 'Golden Gate Park'): 17,
    ('Nob Hill', 'Marina District'): 11,
    ('Nob Hill', 'Russian Hill'): 5,
    # From Embarcadero
    ('Embarcadero', 'Nob Hill'): 10,
    ('Embarcadero', 'The Castro'): 25,
    ('Embarcadero', 'Haight-Ashbury'): 21,
    ('Embarcadero', 'Union Square'): 10,
    ('Embarcadero', 'North Beach'): 5,
    ('Embarcadero', 'Pacific Heights'): 11,
    ('Embarcadero', 'Chinatown'): 7,
    ('Embarcadero', 'Golden Gate Park'): 25,
    ('Embarcadero', 'Marina District'): 12,
    ('Embarcadero', 'Russian Hill'): 8,
    # From The Castro
    ('The Castro', 'Nob Hill'): 16,
    ('The Castro', 'Embarcadero'): 22,
    ('The Castro', 'Haight-Ashbury'): 6,
    ('The Castro', 'Union Square'): 19,
    ('The Castro', 'North Beach'): 20,
    ('The Castro', 'Pacific Heights'): 16,
    ('The Castro', 'Chinatown'): 22,
    ('The Castro', 'Golden Gate Park'): 11,
    ('The Castro', 'Marina District'): 21,
    ('The Castro', 'Russian Hill'): 18,
    # From Haight-Ashbury
    ('Haight-Ashbury', 'Nob Hill'): 15,
    ('Haight-Ashbury', 'Embarcadero'): 20,
    ('Haight-Ashbury', 'The Castro'): 6,
    ('Haight-Ashbury', 'Union Square'): 19,
    ('Haight-Ashbury', 'North Beach'): 19,
    ('Haight-Ashbury', 'Pacific Heights'): 12,
    ('Haight-Ashbury', 'Chinatown'): 19,
    ('Haight-Ashbury', 'Golden Gate Park'): 7,
    ('Haight-Ashbury', 'Marina District'): 17,
    ('Haight-Ashbury', 'Russian Hill'): 17,
    # From Union Square
    ('Union Square', 'Nob Hill'): 9,
    ('Union Square', 'Embarcadero'): 11,
    ('Union Square', 'The Castro'): 17,
    ('Union Square', 'Haight-Ashbury'): 18,
    ('Union Square', 'North Beach'): 10,
    ('Union Square', 'Pacific Heights'): 15,
    ('Union Square', 'Chinatown'): 7,
    ('Union Square', 'Golden Gate Park'): 22,
    ('Union Square', 'Marina District'): 18,
    ('Union Square', 'Russian Hill'): 13,
    # From North Beach
    ('North Beach', 'Nob Hill'): 7,
    ('North Beach', 'Embarcadero'): 6,
    ('North Beach', 'The Castro'): 23,
    ('North Beach', 'Haight-Ashbury'): 18,
    ('North Beach', 'Union Square'): 7,
    ('North Beach', 'Pacific Heights'): 8,
    ('North Beach', 'Chinatown'): 6,
    ('North Beach', 'Golden Gate Park'): 22,
    ('North Beach', 'Marina District'): 9,
    ('North Beach', 'Russian Hill'): 4,
    # From Pacific Heights
    ('Pacific Heights', 'Nob Hill'): 8,
    ('Pacific Heights', 'Embarcadero'): 10,
    ('Pacific Heights', 'The Castro'): 16,
    ('Pacific Heights', 'Haight-Ashbury'): 11,
    ('Pacific Heights', 'Union Square'): 12,
    ('Pacific Heights', 'North Beach'): 9,
    ('Pacific Heights', 'Chinatown'): 11,
    ('Pacific Heights', 'Golden Gate Park'): 15,
    ('Pacific Heights', 'Marina District'): 6,
    ('Pacific Heights', 'Russian Hill'): 7,
    # From Chinatown
    ('Chinatown', 'Nob Hill'): 9,
    ('Chinatown', 'Embarcadero'): 5,
    ('Chinatown', 'The Castro'): 22,
    ('Chinatown', 'Haight-Ashbury'): 19,
    ('Chinatown', 'Union Square'): 7,
    ('Chinatown', 'North Beach'): 3,
    ('Chinatown', 'Pacific Heights'): 10,
    ('Chinatown', 'Golden Gate Park'): 23,
    ('Chinatown', 'Marina District'): 12,
    ('Chinatown', 'Russian Hill'): 7,
    # From Golden Gate Park
    ('Golden Gate Park', 'Nob Hill'): 20,
    ('Golden Gate Park', 'Embarcadero'): 25,
    ('Golden Gate Park', 'The Castro'): 13,
    ('Golden Gate Park', 'Haight-Ashbury'): 7,
    ('Golden Gate Park', 'Union Square'): 22,
    ('Golden Gate Park', 'North Beach'): 23,
    ('Golden Gate Park', 'Pacific Heights'): 16,
    ('Golden Gate Park', 'Chinatown'): 23,
    ('Golden Gate Park', 'Marina District'): 16,
    ('Golden Gate Park', 'Russian Hill'): 19,
    # From Marina District
    ('Marina District', 'Nob Hill'): 12,
    ('Marina District', 'Embarcadero'): 14,
    ('Marina District', 'The Castro'): 22,
    ('Marina District', 'Haight-Ashbury'): 16,
    ('Marina District', 'Union Square'): 16,
    ('Marina District', 'North Beach'): 11,
    ('Marina District', 'Pacific Heights'): 7,
    ('Marina District', 'Chinatown'): 15,
    ('Marina District', 'Golden Gate Park'): 18,
    ('Marina District', 'Russian Hill'): 8,
    # From Russian Hill
    ('Russian Hill', 'Nob Hill'): 5,
    ('Russian Hill', 'Embarcadero'): 8,
    ('Russian Hill', 'The Castro'): 21,
    ('Russian Hill', 'Haight-Ashbury'): 17,
    ('Russian Hill', 'Union Square'): 10,
    ('Russian Hill', 'North Beach'): 5,
    ('Russian Hill', 'Pacific Heights'): 7,
    ('Russian Hill', 'Chinatown'): 9,
    ('Russian Hill', 'Golden Gate Park'): 21,
    ('Russian Hill', 'Marina District'): 7,
}

# Precompute travel times from Nob Hill to each friend's location
nob_to_friend_travel = []
for j in range(10):
    loc_j = friends[j]['location']
    nob_to_friend_travel.append(travel_time[('Nob Hill', loc_j)])

# Precompute travel times between friends' locations
travel_time_matrix = [[0 for _ in range(10)] for _ in range(10)]
for j in range(10):
    for k in range(10):
        loc_j = friends[j]['location']
        loc_k = friends[k]['location']
        travel_time_matrix[j][k] = travel_time[(loc_j, loc_k)]

# Create Z3 solver
s = Optimize()

MAX_EVENTS = 10

# Create variables
friends_vars = []
start_times = []
end_times = []
arrival_times = []
for i in range(MAX_EVENTS):
    friends_vars.append(Int(f'friend_{i}'))
    start_times.append(Int(f'start_{i}'))
    end_times.append(Int(f'end_{i}'))
    arrival_times.append(Int(f'arrival_{i}'))

# Add constraints for each event
for i in range(MAX_EVENTS):
    friend = friends_vars[i]
    start = start_times[i]
    end = end_times[i]
    arrival = arrival_times[i]
    
    # Arrival time computation
    if i == 0:
        # First event: arrival is 9:00 AM + travel time from Nob Hill to friend's location
        arrival_expr = 0
        for j in range(10):
            arrival_expr = If(friend == j, 9 * 60 + nob_to_friend_travel[j], arrival_expr)
        s.add(arrival == arrival_expr)
    else:
        # Subsequent events: arrival is end_{i-1} + travel time between previous and current friend
        # Compute travel time between previous and current friend
        travel_expr = 0
        for j in range(10):
            for k in range(10):
                travel_expr = If(And(friends_vars[i-1] == j, friend == k), travel_time_matrix[j][k], travel_expr)
        s.add(arrival == end_times[i-1] + travel_expr)
    
    # If friend is not -1, then:
    # - previous friend is not -1 (for i >=1)
    if i >= 1:
        s.add(Implies(friend != -1, friends_vars[i-1] != -1))
    
    # Constraints for active friend
    s.add(Implies(friend != -1, start >= arrival))
    s.add(Implies(friend != -1, start >= friends[i]['available_start']))
    s.add(Implies(friend != -1, end == start + friends[i]['required_duration']))
    s.add(Implies(friend != -1, end <= friends[i]['available_end']))

# Ensure each friend is visited at most once
for i in range(MAX_EVENTS):
    for j in range(i + 1, MAX_EVENTS):
        s.add(Or(friends_vars[i] == -1, friends_vars[j] == -1, friends_vars[i] != friends_vars[j]))

# Maximize the number of active friends
count = 0
for i in range(MAX_EVENTS):
    count += If(friends_vars[i] != -1, 1, 0)
s.maximize(count)

# Check for solution
result = s.check()
if result == sat:
    model = s.model()
    # Extract the itinerary
    itinerary = []
    for i in range(MAX_EVENTS):
        friend_idx = model.eval(friends_vars[i])
        if friend_idx != -1:
            friend_idx_val = friend_idx.as_long()
            start_val = model.eval(start_times[i]).as_long()
            end_val = model.eval(end_times[i]).as_long()
            person = friends[friend_idx_val]['name']
            start_time = f"{start_val // 60:02d}:{start_val % 60:02d}"
            end_time = f"{end_val // 60:02d}:{end_val % 60:02d}"
            itinerary.append({"action": "meet", "person": person, "start_time": start_time, "end_time": end_time})
    print(json.dumps({"itinerary": itinerary}))
else:
    print("No solution found.")