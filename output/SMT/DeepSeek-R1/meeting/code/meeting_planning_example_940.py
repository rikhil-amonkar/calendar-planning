from z3 import *

# Define friend data
friends = [
    {'name': 'Kevin', 'location': 'Mission District', 'start_avail': 1245, 'end_avail': 1305, 'min_duration': 60},
    {'name': 'Mark', 'location': 'Fisherman\'s Wharf', 'start_avail': 1035, 'end_avail': 1200, 'min_duration': 90},
    {'name': 'Jessica', 'location': 'Russian Hill', 'start_avail': 540, 'end_avail': 900, 'min_duration': 120},
    {'name': 'Jason', 'location': 'Marina District', 'start_avail': 915, 'end_avail': 1305, 'min_duration': 120},
    {'name': 'John', 'location': 'North Beach', 'start_avail': 585, 'end_avail': 1080, 'min_duration': 15},
    {'name': 'Karen', 'location': 'Chinatown', 'start_avail': 1005, 'end_avail': 1140, 'min_duration': 75},
    {'name': 'Sarah', 'location': 'Pacific Heights', 'start_avail': 1050, 'end_avail': 1095, 'min_duration': 45},
    {'name': 'Amanda', 'location': 'The Castro', 'start_avail': 1200, 'end_avail': 1275, 'min_duration': 60},
    {'name': 'Nancy', 'location': 'Nob Hill', 'start_avail': 585, 'end_avail': 780, 'min_duration': 45},
    {'name': 'Rebecca', 'location': 'Sunset District', 'start_avail': 525, 'end_avail': 900, 'min_duration': 75},
]

# Travel times dictionary
travel_times = {
    ('Union Square', 'Mission District'): 14,
    ('Union Square', 'Fisherman\'s Wharf'): 15,
    ('Union Square', 'Russian Hill'): 13,
    ('Union Square', 'Marina District'): 18,
    ('Union Square', 'North Beach'): 10,
    ('Union Square', 'Chinatown'): 7,
    ('Union Square', 'Pacific Heights'): 15,
    ('Union Square', 'The Castro'): 17,
    ('Union Square', 'Nob Hill'): 9,
    ('Union Square', 'Sunset District'): 27,
    ('Mission District', 'Union Square'): 15,
    ('Mission District', 'Fisherman\'s Wharf'): 22,
    ('Mission District', 'Russian Hill'): 15,
    ('Mission District', 'Marina District'): 19,
    ('Mission District', 'North Beach'): 17,
    ('Mission District', 'Chinatown'): 16,
    ('Mission District', 'Pacific Heights'): 16,
    ('Mission District', 'The Castro'): 7,
    ('Mission District', 'Nob Hill'): 12,
    ('Mission District', 'Sunset District'): 24,
    ('Fisherman\'s Wharf', 'Union Square'): 13,
    ('Fisherman\'s Wharf', 'Mission District'): 22,
    ('Fisherman\'s Wharf', 'Russian Hill'): 7,
    ('Fisherman\'s Wharf', 'Marina District'): 9,
    ('Fisherman\'s Wharf', 'North Beach'): 6,
    ('Fisherman\'s Wharf', 'Chinatown'): 12,
    ('Fisherman\'s Wharf', 'Pacific Heights'): 12,
    ('Fisherman\'s Wharf', 'The Castro'): 27,
    ('Fisherman\'s Wharf', 'Nob Hill'): 11,
    ('Fisherman\'s Wharf', 'Sunset District'): 27,
    ('Russian Hill', 'Union Square'): 10,
    ('Russian Hill', 'Mission District'): 16,
    ('Russian Hill', 'Fisherman\'s Wharf'): 7,
    ('Russian Hill', 'Marina District'): 7,
    ('Russian Hill', 'North Beach'): 5,
    ('Russian Hill', 'Chinatown'): 9,
    ('Russian Hill', 'Pacific Heights'): 7,
    ('Russian Hill', 'The Castro'): 21,
    ('Russian Hill', 'Nob Hill'): 5,
    ('Russian Hill', 'Sunset District'): 23,
    ('Marina District', 'Union Square'): 16,
    ('Marina District', 'Mission District'): 20,
    ('Marina District', 'Fisherman\'s Wharf'): 10,
    ('Marina District', 'Russian Hill'): 8,
    ('Marina District', 'North Beach'): 11,
    ('Marina District', 'Chinatown'): 15,
    ('Marina District', 'Pacific Heights'): 7,
    ('Marina District', 'The Castro'): 22,
    ('Marina District', 'Nob Hill'): 12,
    ('Marina District', 'Sunset District'): 19,
    ('North Beach', 'Union Square'): 7,
    ('North Beach', 'Mission District'): 18,
    ('North Beach', 'Fisherman\'s Wharf'): 5,
    ('North Beach', 'Russian Hill'): 4,
    ('North Beach', 'Marina District'): 9,
    ('North Beach', 'Chinatown'): 6,
    ('North Beach', 'Pacific Heights'): 8,
    ('North Beach', 'The Castro'): 23,
    ('North Beach', 'Nob Hill'): 7,
    ('North Beach', 'Sunset District'): 27,
    ('Chinatown', 'Union Square'): 7,
    ('Chinatown', 'Mission District'): 17,
    ('Chinatown', 'Fisherman\'s Wharf'): 8,
    ('Chinatown', 'Russian Hill'): 7,
    ('Chinatown', 'Marina District'): 12,
    ('Chinatown', 'North Beach'): 3,
    ('Chinatown', 'Pacific Heights'): 10,
    ('Chinatown', 'The Castro'): 22,
    ('Chinatown', 'Nob Hill'): 9,
    ('Chinatown', 'Sunset District'): 29,
    ('Pacific Heights', 'Union Square'): 12,
    ('Pacific Heights', 'Mission District'): 15,
    ('Pacific Heights', 'Fisherman\'s Wharf'): 13,
    ('Pacific Heights', 'Russian Hill'): 7,
    ('Pacific Heights', 'Marina District'): 6,
    ('Pacific Heights', 'North Beach'): 9,
    ('Pacific Heights', 'Chinatown'): 11,
    ('Pacific Heights', 'The Castro'): 16,
    ('Pacific Heights', 'Nob Hill'): 8,
    ('Pacific Heights', 'Sunset District'): 21,
    ('The Castro', 'Union Square'): 19,
    ('The Castro', 'Mission District'): 7,
    ('The Castro', 'Fisherman\'s Wharf'): 24,
    ('The Castro', 'Russian Hill'): 18,
    ('The Castro', 'Marina District'): 21,
    ('The Castro', 'North Beach'): 20,
    ('The Castro', 'Chinatown'): 22,
    ('The Castro', 'Pacific Heights'): 16,
    ('The Castro', 'Nob Hill'): 16,
    ('The Castro', 'Sunset District'): 17,
    ('Nob Hill', 'Union Square'): 7,
    ('Nob Hill', 'Mission District'): 13,
    ('Nob Hill', 'Fisherman\'s Wharf'): 10,
    ('Nob Hill', 'Russian Hill'): 5,
    ('Nob Hill', 'Marina District'): 11,
    ('Nob Hill', 'North Beach'): 8,
    ('Nob Hill', 'Chinatown'): 6,
    ('Nob Hill', 'Pacific Heights'): 8,
    ('Nob Hill', 'The Castro'): 17,
    ('Nob Hill', 'Sunset District'): 24,
    ('Sunset District', 'Union Square'): 30,
    ('Sunset District', 'Mission District'): 25,
    ('Sunset District', 'Fisherman\'s Wharf'): 29,
    ('Sunset District', 'Russian Hill'): 24,
    ('Sunset District', 'Marina District'): 21,
    ('Sunset District', 'North Beach'): 28,
    ('Sunset District', 'Chinatown'): 30,
    ('Sunset District', 'Pacific Heights'): 21,
    ('Sunset District', 'The Castro'): 17,
    ('Sunset District', 'Nob Hill'): 27,
}

# Initialize Z3 variables
opt = Optimize()

# Create variables and constraints for each friend
for friend in friends:
    friend['selected'] = Bool(f'selected_{friend["name"]}')
    friend['start'] = Int(f'start_{friend["name"]}')
    friend['end'] = Int(f'end_{friend["name"]}')
    friend['duration'] = Int(f'duration_{friend["name"]}')
    # Duration and time window constraints
    opt.add(Implies(friend['selected'], 
                    And(friend['start'] >= friend['start_avail'],
                        friend['end'] <= friend['end_avail'],
                        friend['duration'] >= friend['min_duration'],
                        friend['end'] == friend['start'] + friend['duration'])))
    # Start time after arrival from Union Square
    travel_from_us = travel_times[('Union Square', friend['location'])]
    opt.add(Implies(friend['selected'], friend['start'] >= 540 + travel_from_us))

# Pairwise constraints for all friends
for i in range(len(friends)):
    for j in range(i+1, len(friends)):
        fi, fj = friends[i], friends[j]
        loc_i, loc_j = fi['location'], fj['location']
        time_ij = travel_times[(loc_i, loc_j)]
        time_ji = travel_times[(loc_j, loc_i)]
        opt.add(Implies(And(fi['selected'], fj['selected']),
                        Or(fj['start'] >= fi['end'] + time_ij,
                           fi['start'] >= fj['end'] + time_ji)))

# Maximize the number of friends met
total_selected = Sum([If(f['selected'], 1, 0) for f in friends])
opt.maximize(total_selected)

# Solve and output
if opt.check() == sat:
    model = opt.model()
    selected = []
    for friend in friends:
        if model.evaluate(friend['selected']):
            start = model.evaluate(friend['start']).as_long()
            end = model.evaluate(friend['end']).as_long()
            start_hr = f"{start//60:02}:{start%60:02}"
            end_hr = f"{end//60:02}:{end%60:02}"
            selected.append((friend['name'], start_hr, end_hr))
    print(f"Maximum friends met: {len(selected)}")
    for name, s, e in selected:
        print(f"{name}: {s} - {e}")
else:
    print("No valid schedule found.")