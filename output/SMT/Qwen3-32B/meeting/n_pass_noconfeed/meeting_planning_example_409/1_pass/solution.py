import z3
import json

# Define friends and their constraints
friends = [
    {'name': 'Laura', 'location': 'Nob Hill', 'available_start': 525, 'available_end': 975, 'min_duration': 30},
    {'name': 'Thomas', 'location': 'Bayview', 'available_start': 930, 'available_end': 1110, 'min_duration': 120},
    {'name': 'Stephanie', 'location': 'Golden Gate Park', 'available_start': 1110, 'available_end': 1305, 'min_duration': 30},
    {'name': 'Betty', 'location': 'Marina District', 'available_start': 1125, 'available_end': 1305, 'min_duration': 45},
    {'name': 'Patricia', 'location': 'Embarcadero', 'available_start': 1050, 'available_end': 1320, 'min_duration': 45},
]

# Define travel times between locations
travel_time = {
    ('Fisherman\'s Wharf', 'Bayview'): 26,
    ('Fisherman\'s Wharf', 'Golden Gate Park'): 25,
    ('Fisherman\'s Wharf', 'Nob Hill'): 11,
    ('Fisherman\'s Wharf', 'Marina District'): 9,
    ('Fisherman\'s Wharf', 'Embarcadero'): 8,
    ('Bayview', 'Fisherman\'s Wharf'): 25,
    ('Bayview', 'Golden Gate Park'): 22,
    ('Bayview', 'Nob Hill'): 20,
    ('Bayview', 'Marina District'): 25,
    ('Bayview', 'Embarcadero'): 19,
    ('Golden Gate Park', 'Fisherman\'s Wharf'): 24,
    ('Golden Gate Park', 'Bayview'): 23,
    ('Golden Gate Park', 'Nob Hill'): 20,
    ('Golden Gate Park', 'Marina District'): 16,
    ('Golden Gate Park', 'Embarcadero'): 25,
    ('Nob Hill', 'Fisherman\'s Wharf'): 11,
    ('Nob Hill', 'Bayview'): 19,
    ('Nob Hill', 'Golden Gate Park'): 17,
    ('Nob Hill', 'Marina District'): 11,
    ('Nob Hill', 'Embarcadero'): 9,
    ('Marina District', 'Fisherman\'s Wharf'): 10,
    ('Marina District', 'Bayview'): 27,
    ('Marina District', 'Golden Gate Park'): 18,
    ('Marina District', 'Nob Hill'): 12,
    ('Marina District', 'Embarcadero'): 14,
    ('Embarcadero', 'Fisherman\'s Wharf'): 6,
    ('Embarcadero', 'Bayview'): 21,
    ('Embarcadero', 'Golden Gate Park'): 25,
    ('Embarcadero', 'Nob Hill'): 10,
    ('Embarcadero', 'Marina District'): 12,
}

# Create Z3 solver
solver = z3.Optimize()

# Create variables for each friend
met = []
start = []
order = []
for i in range(5):
    met_i = z3.Bool(f'met_{i}')
    start_i = z3.Int(f'start_{i}')
    order_i = z3.Int(f'order_{i}')
    met.append(met_i)
    start.append(start_i)
    order.append(order_i)

# Add constraints for each friend
for i in range(5):
    friend = friends[i]
    loc = friend['location']
    available_start = friend['available_start']
    available_end = friend['available_end']
    min_duration = friend['min_duration']
    # If met_i is True, start_i is within available time and duration
    solver.add(z3.Implies(met[i], start[i] >= available_start))
    solver.add(z3.Implies(met[i], start[i] + min_duration <= available_end))
    # First meeting constraint: if order_i == 0 and met_i is True, start_i >= arrival time
    arrival_time = 540 + travel_time[('Fisherman\'s Wharf', loc)]
    solver.add(z3.Implies(z3.And(met[i], order[i] == 0), start[i] >= arrival_time))

# Add constraints for pairs of friends
for i in range(5):
    for j in range(i+1, 5):
        loc_i = friends[i]['location']
        loc_j = friends[j]['location']
        travel_i_j = travel_time[(loc_i, loc_j)]
        travel_j_i = travel_time[(loc_j, loc_i)]
        min_duration_i = friends[i]['min_duration']
        min_duration_j = friends[j]['min_duration']
        # Constraints if both are met
        solver.add(z3.Implies(z3.And(met[i], met[j]), order[i] != order[j]))
        solver.add(z3.Implies(z3.And(met[i], met[j], order[i] < order[j]), 
                               start[i] + min_duration_i + travel_i_j <= start[j]))
        solver.add(z3.Implies(z3.And(met[i], met[j], order[j] < order[i]), 
                               start[j] + min_duration_j + travel_j_i <= start[i]))

# Maximize the number of met friends
solver.maximize(z3.Sum([z3.If(met[i], 1, 0) for i in range(5)]))

# Check if the problem is satisfiable
if solver.check() == z3.sat:
    model = solver.model()
    met_friends = []
    for i in range(5):
        if model.eval(met[i]):
            friend_data = friends[i]
            start_time = model.eval(start[i]).as_long()
            end_time = start_time + friend_data['min_duration']
            order_val = model.eval(order[i]).as_long()
            met_friends.append((order_val, {
                'name': friend_data['name'],
                'location': friend_data['location'],
                'start_time': start_time,
                'end_time': end_time
            }))
    # Sort by order
    met_friends.sort()
    itinerary = []
    for order_val, friend in met_friends:
        def to_time_str(minutes):
            hours = minutes // 60
            mins = minutes % 60
            return f"{hours}:{mins:02d}"
        itinerary.append({
            "action": "meet",
            "location": friend['location'],
            "person": friend['name'],
            "start_time": to_time_str(friend['start_time']),
            "end_time": to_time_str(friend['end_time'])
        })
    print(json.dumps({"itinerary": itinerary}, indent=2))
else:
    print("No solution found.")