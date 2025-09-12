import z3
import json

# Define friends and their constraints
friends = [
    {'name': 'Emily', 'location': 'Pacific Heights', 'available_start': 555, 'available_end': 825, 'duration': 120},
    {'name': 'Helen', 'location': 'North Beach', 'available_start': 825, 'available_end': 1125, 'duration': 30},
    {'name': 'Kimberly', 'location': 'Golden Gate Park', 'available_start': 1125, 'available_end': 1275, 'duration': 75},
    {'name': 'James', 'location': 'Embarcadero', 'available_start': 630, 'available_end': 690, 'duration': 30},
    {'name': 'Linda', 'location': 'Haight-Ashbury', 'available_start': 450, 'available_end': 1155, 'duration': 15},
    {'name': 'Paul', 'location': "Fisherman's Wharf", 'available_start': 885, 'available_end': 1125, 'duration': 90},
    {'name': 'Anthony', 'location': 'Mission District', 'available_start': 480, 'available_end': 885, 'duration': 105},
    {'name': 'Nancy', 'location': 'Alamo Square', 'available_start': 510, 'available_end': 825, 'duration': 120},
    {'name': 'William', 'location': 'Bayview', 'available_start': 1050, 'available_end': 1230, 'duration': 120},
    {'name': 'Margaret', 'location': 'Richmond District', 'available_start': 915, 'available_end': 1095, 'duration': 45},
]

# Define travel times between locations
locations = [
    'Russian Hill',
    'Pacific Heights',
    'North Beach',
    'Golden Gate Park',
    'Embarcadero',
    'Haight-Ashbury',
    "Fisherman's Wharf",
    'Mission District',
    'Alamo Square',
    'Bayview',
    'Richmond District'
]

travel_times = {
    # Russian Hill to others
    ('Russian Hill', 'Pacific Heights'): 7,
    ('Russian Hill', 'North Beach'): 5,
    ('Russian Hill', 'Golden Gate Park'): 21,
    ('Russian Hill', 'Embarcadero'): 8,
    ('Russian Hill', 'Haight-Ashbury'): 17,
    ('Russian Hill', "Fisherman's Wharf"): 7,
    ('Russian Hill', 'Mission District'): 16,
    ('Russian Hill', 'Alamo Square'): 15,
    ('Russian Hill', 'Bayview'): 23,
    ('Russian Hill', 'Richmond District'): 14,
    # Pacific Heights to others
    ('Pacific Heights', 'Russian Hill'): 7,
    ('Pacific Heights', 'North Beach'): 9,
    ('Pacific Heights', 'Golden Gate Park'): 15,
    ('Pacific Heights', 'Embarcadero'): 10,
    ('Pacific Heights', 'Haight-Ashbury'): 11,
    ('Pacific Heights', "Fisherman's Wharf"): 13,
    ('Pacific Heights', 'Mission District'): 15,
    ('Pacific Heights', 'Alamo Square'): 10,
    ('Pacific Heights', 'Bayview'): 22,
    ('Pacific Heights', 'Richmond District'): 12,
    # North Beach to others
    ('North Beach', 'Russian Hill'): 4,
    ('North Beach', 'Pacific Heights'): 8,
    ('North Beach', 'Golden Gate Park'): 22,
    ('North Beach', 'Embarcadero'): 6,
    ('North Beach', 'Haight-Ashbury'): 18,
    ('North Beach', "Fisherman's Wharf"): 5,
    ('North Beach', 'Mission District'): 18,
    ('North Beach', 'Alamo Square'): 16,
    ('North Beach', 'Bayview'): 25,
    ('North Beach', 'Richmond District'): 18,
    # Golden Gate Park to others
    ('Golden Gate Park', 'Russian Hill'): 19,
    ('Golden Gate Park', 'Pacific Heights'): 16,
    ('Golden Gate Park', 'North Beach'): 23,
    ('Golden Gate Park', 'Embarcadero'): 25,
    ('Golden Gate Park', 'Haight-Ashbury'): 7,
    ('Golden Gate Park', "Fisherman's Wharf"): 24,
    ('Golden Gate Park', 'Mission District'): 17,
    ('Golden Gate Park', 'Alamo Square'): 9,
    ('Golden Gate Park', 'Bayview'): 23,
    ('Golden Gate Park', 'Richmond District'): 7,
    # Embarcadero to others
    ('Embarcadero', 'Russian Hill'): 8,
    ('Embarcadero', 'Pacific Heights'): 11,
    ('Embarcadero', 'North Beach'): 5,
    ('Embarcadero', 'Golden Gate Park'): 25,
    ('Embarcadero', 'Haight-Ashbury'): 21,
    ('Embarcadero', "Fisherman's Wharf"): 6,
    ('Embarcadero', 'Mission District'): 20,
    ('Embarcadero', 'Alamo Square'): 19,
    ('Embarcadero', 'Bayview'): 21,
    ('Embarcadero', 'Richmond District'): 21,
    # Haight-Ashbury to others
    ('Haight-Ashbury', 'Russian Hill'): 17,
    ('Haight-Ashbury', 'Pacific Heights'): 12,
    ('Haight-Ashbury', 'North Beach'): 19,
    ('Haight-Ashbury', 'Golden Gate Park'): 7,
    ('Haight-Ashbury', 'Embarcadero'): 20,
    ('Haight-Ashbury', "Fisherman's Wharf"): 23,
    ('Haight-Ashbury', 'Mission District'): 11,
    ('Haight-Ashbury', 'Alamo Square'): 5,
    ('Haight-Ashbury', 'Bayview'): 18,
    ('Haight-Ashbury', 'Richmond District'): 10,
    # Fisherman's Wharf to others
    ("Fisherman's Wharf", 'Russian Hill'): 7,
    ("Fisherman's Wharf", 'Pacific Heights'): 12,
    ("Fisherman's Wharf", 'North Beach'): 6,
    ("Fisherman's Wharf", 'Golden Gate Park'): 25,
    ("Fisherman's Wharf", 'Embarcadero'): 8,
    ("Fisherman's Wharf", 'Haight-Ashbury'): 22,
    ("Fisherman's Wharf", 'Mission District'): 22,
    ("Fisherman's Wharf", 'Alamo Square'): 21,
    ("Fisherman's Wharf", 'Bayview'): 26,
    ("Fisherman's Wharf", 'Richmond District'): 18,
    # Mission District to others
    ('Mission District', 'Russian Hill'): 15,
    ('Mission District', 'Pacific Heights'): 16,
    ('Mission District', 'North Beach'): 17,
    ('Mission District', 'Golden Gate Park'): 17,
    ('Mission District', 'Embarcadero'): 19,
    ('Mission District', 'Haight-Ashbury'): 12,
    ('Mission District', "Fisherman's Wharf"): 22,
    ('Mission District', 'Alamo Square'): 11,
    ('Mission District', 'Bayview'): 14,
    ('Mission District', 'Richmond District'): 20,
    # Alamo Square to others
    ('Alamo Square', 'Russian Hill'): 13,
    ('Alamo Square', 'Pacific Heights'): 10,
    ('Alamo Square', 'North Beach'): 15,
    ('Alamo Square', 'Golden Gate Park'): 9,
    ('Alamo Square', 'Embarcadero'): 16,
    ('Alamo Square', 'Haight-Ashbury'): 5,
    ('Alamo Square', "Fisherman's Wharf"): 19,
    ('Alamo Square', 'Mission District'): 10,
    ('Alamo Square', 'Bayview'): 16,
    ('Alamo Square', 'Richmond District'): 11,
    # Bayview to others
    ('Bayview', 'Russian Hill'): 23,
    ('Bayview', 'Pacific Heights'): 23,
    ('Bayview', 'North Beach'): 22,
    ('Bayview', 'Golden Gate Park'): 22,
    ('Bayview', 'Embarcadero'): 19,
    ('Bayview', 'Haight-Ashbury'): 19,
    ('Bayview', "Fisherman's Wharf"): 25,
    ('Bayview', 'Mission District'): 13,
    ('Bayview', 'Alamo Square'): 16,
    ('Bayview', 'Richmond District'): 25,
    # Richmond District to others
    ('Richmond District', 'Russian Hill'): 13,
    ('Richmond District', 'Pacific Heights'): 10,
    ('Richmond District', 'North Beach'): 17,
    ('Richmond District', 'Golden Gate Park'): 9,
    ('Richmond District', 'Embarcadero'): 19,
    ('Richmond District', 'Haight-Ashbury'): 10,
    ('Richmond District', "Fisherman's Wharf"): 18,
    ('Richmond District', 'Mission District'): 20,
    ('Richmond District', 'Alamo Square'): 13,
    ('Richmond District', 'Bayview'): 27,
}

# Z3 variables
num_friends = len(friends)
met_vars = [z3.Bool(f'met_{i}') for i in range(num_friends)]
start_vars = [z3.Int(f'start_{i}') for i in range(num_friends)]
end_vars = [z3.Int(f'end_{i}') for i in range(num_friends)]
prev_vars = [z3.Int(f'prev_{i}') for i in range(num_friends)]
arrival_vars = [z3.Int(f'arrival_{i}') for i in range(num_friends)]

solver = z3.Optimize()

# Add constraints for each friend
for i in range(num_friends):
    # If met, then start >= available_start
    solver.add(z3.Implies(met_vars[i], start_vars[i] >= friends[i]['available_start']))
    # If met, then end = start + duration
    solver.add(z3.Implies(met_vars[i], end_vars[i] == start_vars[i] + friends[i]['duration']))
    # If met, then end <= available_end
    solver.add(z3.Implies(met_vars[i], end_vars[i] <= friends[i]['available_end']))
    # If met, then arrival <= start
    solver.add(z3.Implies(met_vars[i], arrival_vars[i] <= start_vars[i]))

    # Add constraints for arrival time based on prev
    for B in range(-1, num_friends):
        if B == -1:
            loc_from = 'Russian Hill'
            loc_to = friends[i]['location']
            time = travel_times[(loc_from, loc_to)]
            arrival_val = 540 + time
        else:
            loc_from = friends[B]['location']
            loc_to = friends[i]['location']
            time = travel_times[(loc_from, loc_to)]
            arrival_val = end_vars[B] + time
        solver.add(z3.Implies(prev_vars[i] == B, arrival_vars[i] == arrival_val))

    # Ensure that if prev is B (not -1), then met_B is true
    for B in range(num_friends):
        solver.add(z3.Implies(prev_vars[i] == B, met_vars[B]))

# Maximize the number of met friends
objective = z3.Sum([z3.If(met_vars[i], 1, 0) for i in range(num_friends)])
solver.maximize(objective)

# Solve and output result
if solver.check() == z3.sat:
    model = solver.model()
    met_friends = [i for i in range(num_friends) if model.eval(met_vars[i])]
    first = None
    for i in met_friends:
        if model.eval(prev_vars[i]) == -1:
            first = i
            break
    itinerary = []
    current = first
    while current is not None:
        start_time = model.eval(start_vars[current]).as_long()
        end_time = model.eval(end_vars[current]).as_long()
        name = friends[current]['name']
        location = friends[current]['location']
        itinerary.append({
            'action': 'meet',
            'location': location,
            'person': name,
            'start_time': f"{start_time//60}:{start_time%60:02d}",
            'end_time': f"{end_time//60}:{end_time%60:02d}"
        })
        next_prev = None
        for j in met_friends:
            if model.eval(prev_vars[j]) == current:
                next_prev = j
                break
        current = next_prev
    print(json.dumps({"itinerary": itinerary}))
else:
    print(json.dumps({"itinerary": []}))