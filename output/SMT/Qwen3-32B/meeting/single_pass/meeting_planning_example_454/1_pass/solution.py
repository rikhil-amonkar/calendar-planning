from z3 import *
import json

# Define friends and their parameters
friends = [
    {
        'name': 'Daniel',
        'location': 'Mission District',
        'available_start': 7 * 60,  # 7:00 AM
        'available_end': 11 * 60 + 15,  # 11:15 AM
        'required_duration': 105
    },
    {
        'name': 'Ronald',
        'location': 'Chinatown',
        'available_start': 7 * 60 + 15,  # 7:15 AM
        'available_end': 14 * 60 + 45,  # 2:45 PM
        'required_duration': 90
    },
    {
        'name': 'William',
        'location': 'North Beach',
        'available_start': 13 * 60 + 15,  # 1:15 PM
        'available_end': 20 * 60 + 15,  # 8:15 PM
        'required_duration': 15
    },
    {
        'name': 'Jessica',
        'location': 'Golden Gate Park',
        'available_start': 13 * 60 + 45,  # 1:45 PM
        'available_end': 15 * 60,  # 3:00 PM
        'required_duration': 30
    },
    {
        'name': 'Ashley',
        'location': 'Bayview',
        'available_start': 17 * 60 + 15,  # 5:15 PM
        'available_end': 20 * 60,  # 8:00 PM
        'required_duration': 105
    }
]

# Travel times from Presidio to each location
presidio_travel_times = {
    'Presidio': 0,
    'Golden Gate Park': 12,
    'Bayview': 31,
    'Chinatown': 21,
    'North Beach': 18,
    'Mission District': 26
}

# Define all travel times between locations
travel_times = {
    ('Presidio', 'Golden Gate Park'): 12,
    ('Presidio', 'Bayview'): 31,
    ('Presidio', 'Chinatown'): 21,
    ('Presidio', 'North Beach'): 18,
    ('Presidio', 'Mission District'): 26,
    ('Golden Gate Park', 'Presidio'): 11,
    ('Golden Gate Park', 'Bayview'): 23,
    ('Golden Gate Park', 'Chinatown'): 23,
    ('Golden Gate Park', 'North Beach'): 24,
    ('Golden Gate Park', 'Mission District'): 17,
    ('Bayview', 'Presidio'): 31,
    ('Bayview', 'Golden Gate Park'): 22,
    ('Bayview', 'Chinatown'): 18,
    ('Bayview', 'North Beach'): 21,
    ('Bayview', 'Mission District'): 13,
    ('Chinatown', 'Presidio'): 19,
    ('Chinatown', 'Golden Gate Park'): 23,
    ('Chinatown', 'Bayview'): 22,
    ('Chinatown', 'North Beach'): 3,
    ('Chinatown', 'Mission District'): 18,
    ('North Beach', 'Presidio'): 17,
    ('North Beach', 'Golden Gate Park'): 22,
    ('North Beach', 'Bayview'): 22,
    ('North Beach', 'Chinatown'): 6,
    ('North Beach', 'Mission District'): 18,
    ('Mission District', 'Presidio'): 25,
    ('Mission District', 'Golden Gate Park'): 17,
    ('Mission District', 'Bayview'): 15,
    ('Mission District', 'Chinatown'): 16,
    ('Mission District', 'North Beach'): 17,
}

# Create Z3 variables for each friend
met_vars = {}
start_vars = {}
end_vars = {}
order_vars = {}

for friend in friends:
    name = friend['name']
    met_vars[name] = Bool(f'met_{name}')
    start_vars[name] = Int(f'start_{name}')
    end_vars[name] = Int(f'end_{name}')
    order_vars[name] = Int(f'order_{name}')

solver = Optimize()

# Add constraints for each friend
for friend in friends:
    name = friend['name']
    loc = friend['location']
    available_start = friend['available_start']
    available_end = friend['available_end']
    required_duration = friend['required_duration']
    
    met = met_vars[name]
    start = start_vars[name]
    end = end_vars[name]
    
    # If met, then start and end times are within available window and duration
    solver.add(Implies(met, start >= available_start))
    solver.add(Implies(met, end <= available_end))
    solver.add(Implies(met, end - start >= required_duration))
    
    # If met and is the first meeting (order == 0), then start >= 9:00AM + travel time
    travel_time = presidio_travel_times[loc]
    solver.add(Implies(And(met, order_vars[name] == 0), start >= 9 * 60 + travel_time))

# Add constraints between pairs of friends
for i in range(len(friends)):
    for j in range(len(friends)):
        if i == j:
            continue
        friendA = friends[i]
        friendB = friends[j]
        nameA = friendA['name']
        nameB = friendB['name']
        locA = friendA['location']
        locB = friendB['location']
        metA = met_vars[nameA]
        metB = met_vars[nameB]
        orderA = order_vars[nameA]
        orderB = order_vars[nameB]
        startA = start_vars[nameA]
        endA = end_vars[nameA]
        startB = start_vars[nameB]
        endB = end_vars[nameB]
        
        # Get travel time from A's location to B's location
        key = (locA, locB)
        if key in travel_times:
            ttAB = travel_times[key]
        else:
            # This shouldn't happen as all pairs are given
            ttAB = 0  # Placeholder, but should not be needed
        
        # Add constraints for orderA < orderB
        solver.add(Implies(And(metA, metB, orderA < orderB), endA + ttAB <= startB))
        
        # Add constraints for orderB < orderA
        solver.add(Implies(And(metB, metA, orderB < orderA), endB + travel_times[(locB, locA)] <= startA))
        
        # Ensure that if both are met, their order is different
        solver.add(Implies(And(metA, metB), orderA != orderB))

# Maximize the number of friends met
num_friends = len(friends)
solver.maximize(Sum([If(met_vars[name], 1, 0) for name in met_vars]))

# Check if the problem is satisfiable
result = solver.check()
if result == sat:
    model = solver.model()
    # Extract the met friends and their meeting times
    itinerary = []
    for friend in friends:
        name = friend['name']
        met = model.eval(met_vars[name])
        if met:
            start = model.eval(start_vars[name])
            end = model.eval(end_vars[name])
            start_time = f"{(start // 60):02d}:{(start % 60):02d}"
            end_time = f"{(end // 60):02d}:{(end % 60):02d}"
            itinerary.append({"action": "meet", "person": name, "start_time": start_time, "end_time": end_time})
    # Sort the itinerary by start time
    itinerary.sort(key=lambda x: int(x['start_time'].replace(':', '')))
    print(json.dumps({"itinerary": itinerary}))
else:
    print("No solution found.")