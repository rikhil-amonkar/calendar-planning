from z3 import *
from itertools import combinations

# Define friends with their details
friends = [
    {'name': 'Kevin', 'location': 'Mission District', 'available_start': 1245, 'available_end': 1305, 'duration': 60},
    {'name': 'Mark', 'location': 'Fisherman\'s Wharf', 'available_start': 1035, 'available_end': 1200, 'duration': 90},
    {'name': 'Jessica', 'location': 'Russian Hill', 'available_start': 540, 'available_end': 900, 'duration': 120},
    {'name': 'Jason', 'location': 'Marina District', 'available_start': 915, 'available_end': 1305, 'duration': 120},
    {'name': 'John', 'location': 'North Beach', 'available_start': 585, 'available_end': 1080, 'duration': 15},
    {'name': 'Karen', 'location': 'Chinatown', 'available_start': 1005, 'available_end': 1140, 'duration': 75},
    {'name': 'Sarah', 'location': 'Pacific Heights', 'available_start': 1050, 'available_end': 1095, 'duration': 45},
    {'name': 'Amanda', 'location': 'The Castro', 'available_start': 1200, 'available_end': 1275, 'duration': 60},
    {'name': 'Nancy', 'location': 'Nob Hill', 'available_start': 585, 'available_end': 780, 'duration': 45},
    {'name': 'Rebecca', 'location': 'Sunset District', 'available_start': 525, 'available_end': 900, 'duration': 75}
]

# Create Z3 variables for each friend
for friend in friends:
    friend['met'] = Bool(friend['name'])
    friend['start'] = Int(f'start_{friend["name"]}')
    friend['end'] = Int(f'end_{friend["name"]}')

# Define travel_time dictionary (abbreviated for brevity, all entries must be present)
travel_time = {
    ('Union Square', 'Mission District'): 14,
    ('Mission District', 'Union Square'): 15,
    ('Union Square', 'Fisherman\'s Wharf'): 15,
    ('Fisherman\'s Wharf', 'Union Square'): 13,
    ('Union Square', 'Russian Hill'): 13,
    ('Russian Hill', 'Union Square'): 10,
    ('Union Square', 'Marina District'): 18,
    ('Marina District', 'Union Square'): 16,
    ('Union Square', 'North Beach'): 10,
    ('North Beach', 'Union Square'): 7,
    ('Union Square', 'Chinatown'): 7,
    ('Chinatown', 'Union Square'): 7,
    ('Union Square', 'Pacific Heights'): 15,
    ('Pacific Heights', 'Union Square'): 12,
    ('Union Square', 'The Castro'): 17,
    ('The Castro', 'Union Square'): 19,
    ('Union Square', 'Nob Hill'): 9,
    ('Nob Hill', 'Union Square'): 7,
    ('Union Square', 'Sunset District'): 27,
    ('Sunset District', 'Union Square'): 30,
    ('Mission District', 'Fisherman\'s Wharf'): 22,
    ('Fisherman\'s Wharf', 'Mission District'): 22,
    ('Mission District', 'Russian Hill'): 15,
    ('Russian Hill', 'Mission District'): 16,
    ('Mission District', 'Marina District'): 19,
    ('Marina District', 'Mission District'): 20,
    ('Mission District', 'North Beach'): 17,
    ('North Beach', 'Mission District'): 18,
    ('Mission District', 'Chinatown'): 16,
    ('Chinatown', 'Mission District'): 17,
    ('Mission District', 'Pacific Heights'): 16,
    ('Pacific Heights', 'Mission District'): 15,
    ('Mission District', 'The Castro'): 7,
    ('The Castro', 'Mission District'): 7,
    ('Mission District', 'Nob Hill'): 12,
    ('Nob Hill', 'Mission District'): 13,
    ('Mission District', 'Sunset District'): 24,
    ('Sunset District', 'Mission District'): 25,
    ('Fisherman\'s Wharf', 'Russian Hill'): 7,
    ('Russian Hill', 'Fisherman\'s Wharf'): 7,
    ('Fisherman\'s Wharf', 'Marina District'): 9,
    ('Marina District', 'Fisherman\'s Wharf'): 10,
    ('Fisherman\'s Wharf', 'North Beach'): 6,
    ('North Beach', 'Fisherman\'s Wharf'): 5,
    ('Fisherman\'s Wharf', 'Chinatown'): 12,
    ('Chinatown', 'Fisherman\'s Wharf'): 8,
    ('Fisherman\'s Wharf', 'Pacific Heights'): 12,
    ('Pacific Heights', 'Fisherman\'s Wharf'): 13,
    ('Fisherman\'s Wharf', 'The Castro'): 27,
    ('The Castro', 'Fisherman\'s Wharf'): 24,
    ('Fisherman\'s Wharf', 'Nob Hill'): 11,
    ('Nob Hill', 'Fisherman\'s Wharf'): 10,
    ('Fisherman\'s Wharf', 'Sunset District'): 27,
    ('Sunset District', 'Fisherman\'s Wharf'): 29,
    ('Russian Hill', 'Marina District'): 7,
    ('Marina District', 'Russian Hill'): 8,
    ('Russian Hill', 'North Beach'): 5,
    ('North Beach', 'Russian Hill'): 4,
    ('Russian Hill', 'Chinatown'): 9,
    ('Chinatown', 'Russian Hill'): 7,
    ('Russian Hill', 'Pacific Heights'): 7,
    ('Pacific Heights', 'Russian Hill'): 7,
    ('Russian Hill', 'The Castro'): 21,
    ('The Castro', 'Russian Hill'): 18,
    ('Russian Hill', 'Nob Hill'): 5,
    ('Nob Hill', 'Russian Hill'): 5,
    ('Russian Hill', 'Sunset District'): 23,
    ('Sunset District', 'Russian Hill'): 24,
    ('Marina District', 'North Beach'): 11,
    ('North Beach', 'Marina District'): 9,
    ('Marina District', 'Chinatown'): 15,
    ('Chinatown', 'Marina District'): 12,
    ('Marina District', 'Pacific Heights'): 7,
    ('Pacific Heights', 'Marina District'): 6,
    ('Marina District', 'The Castro'): 22,
    ('The Castro', 'Marina District'): 21,
    ('Marina District', 'Nob Hill'): 12,
    ('Nob Hill', 'Marina District'): 11,
    ('Marina District', 'Sunset District'): 19,
    ('Sunset District', 'Marina District'): 21,
    ('North Beach', 'Chinatown'): 6,
    ('Chinatown', 'North Beach'): 3,
    ('North Beach', 'Pacific Heights'): 8,
    ('Pacific Heights', 'North Beach'): 9,
    ('North Beach', 'The Castro'): 23,
    ('The Castro', 'North Beach'): 20,
    ('North Beach', 'Nob Hill'): 7,
    ('Nob Hill', 'North Beach'): 8,
    ('North Beach', 'Sunset District'): 27,
    ('Sunset District', 'North Beach'): 28,
    ('Chinatown', 'Pacific Heights'): 10,
    ('Pacific Heights', 'Chinatown'): 11,
    ('Chinatown', 'The Castro'): 22,
    ('The Castro', 'Chinatown'): 22,
    ('Chinatown', 'Nob Hill'): 9,
    ('Nob Hill', 'Chinatown'): 6,
    ('Chinatown', 'Sunset District'): 29,
    ('Sunset District', 'Chinatown'): 30,
    ('Pacific Heights', 'The Castro'): 16,
    ('The Castro', 'Pacific Heights'): 16,
    ('Pacific Heights', 'Nob Hill'): 8,
    ('Nob Hill', 'Pacific Heights'): 8,
    ('Pacific Heights', 'Sunset District'): 21,
    ('Sunset District', 'Pacific Heights'): 21,
    ('The Castro', 'Nob Hill'): 16,
    ('Nob Hill', 'The Castro'): 17,
    ('The Castro', 'Sunset District'): 17,
    ('Sunset District', 'The Castro'): 17,
    ('Nob Hill', 'Sunset District'): 24,
    ('Sunset District', 'Nob Hill'): 27,
}

solver = Solver()

# Add individual friend constraints
for friend in friends:
    met = friend['met']
    start = friend['start']
    end = friend['end']
    available_start = friend['available_start']
    available_end = friend['available_end']
    duration = friend['duration']
    location = friend['location']

    # Availability and duration constraints
    solver.add(Implies(met, start >= available_start))
    solver.add(Implies(met, end <= available_end))
    solver.add(Implies(met, end == start + duration))

    # Start time must be at least arrival from Union Square
    union_to_loc = travel_time[('Union Square', location)]
    solver.add(Implies(met, start >= 540 + union_to_loc))

# Add pairwise constraints for travel and order
for a, b in combinations(friends, 2):
    a_before_b = Bool(f"{a['name']}_before_{b['name']}")

    travel_ab = travel_time[(a['location'], b['location'])]
    travel_ba = travel_time[(b['location'], a['location'])]

    # If both are met, enforce order and travel time
    solver.add(Implies(And(a['met'], b['met'], a_before_b), a['end'] + travel_ab <= b['start'])
    solver.add(Implies(And(a['met'], b['met'], Not(a_before_b)), b['end'] + travel_ba <= a['start']))

# Maximize the number of friends met
max_friends = Sum([If(friend['met'], 1, 0) for friend in friends])
solver.maximize(max_friends)

# Check and print the solution
if solver.check() == sat:
    model = solver.model()
    schedule = []
    for friend in friends:
        if model.eval(friend['met']):
            start = model.eval(friend['start'])
            end = model.eval(friend['end'])
            schedule.append((friend['name'], start.as_long(), end.as_long()))
    schedule.sort(key=lambda x: x[1])
    print("Optimal Schedule:")
    for name, start, end in schedule:
        sh, sm = divmod(start, 60)
        eh, em = divmod(end, 60)
        print(f"{name}: {sh:02d}:{sm:02d}-{eh:02d}:{em:02d}")
else:
    print("No valid schedule found.")