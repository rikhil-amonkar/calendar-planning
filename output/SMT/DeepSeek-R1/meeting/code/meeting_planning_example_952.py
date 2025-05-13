from z3 import *
from itertools import combinations

friends = [
    {'name': 'Start', 'location': 'Bayview', 'available_start': 540, 'available_end': 540, 'duration': 0},
    {'name': 'Brian', 'location': 'North Beach', 'available_start': 780, 'available_end': 1140, 'duration': 90},
    {'name': 'Richard', 'location': "Fisherman's Wharf", 'available_start': 660, 'available_end': 765, 'duration': 60},
    {'name': 'Ashley', 'location': 'Haight-Ashbury', 'available_start': 900, 'available_end': 1230, 'duration': 90},
    {'name': 'Elizabeth', 'location': 'Nob Hill', 'available_start': 705, 'available_end': 1110, 'duration': 75},
    {'name': 'Jessica', 'location': 'Golden Gate Park', 'available_start': 1200, 'available_end': 1305, 'duration': 105},
    {'name': 'Deborah', 'location': 'Union Square', 'available_start': 1050, 'available_end': 1320, 'duration': 60},
    {'name': 'Kimberly', 'location': 'Alamo Square', 'available_start': 1050, 'available_end': 1275, 'duration': 45},
    {'name': 'Kenneth', 'location': 'Chinatown', 'available_start': 825, 'available_end': 1170, 'duration': 105},
    {'name': 'Anthony', 'location': 'Pacific Heights', 'available_start': 855, 'available_end': 960, 'duration': 30},
]

for friend in friends:
    friend['met'] = Bool(friend['name'])
    friend['start'] = Int(f'start_{friend["name"]}')
    friend['end'] = Int(f'end_{friend["name"]}')

travel_time = {
    ('Bayview', 'North Beach'): 22,
    ('Bayview', "Fisherman's Wharf"): 25,
    ('Bayview', 'Haight-Ashbury'): 19,
    ('Bayview', 'Nob Hill'): 20,
    ('Bayview', 'Golden Gate Park'): 22,
    ('Bayview', 'Union Square'): 18,
    ('Bayview', 'Alamo Square'): 16,
    ('Bayview', 'Presidio'): 32,
    ('Bayview', 'Chinatown'): 19,
    ('Bayview', 'Pacific Heights'): 23,
    ('North Beach', 'Bayview'): 25,
    ('North Beach', "Fisherman's Wharf"): 5,
    ('North Beach', 'Haight-Ashbury'): 18,
    ('North Beach', 'Nob Hill'): 7,
    ('North Beach', 'Golden Gate Park'): 22,
    ('North Beach', 'Union Square'): 7,
    ('North Beach', 'Alamo Square'): 16,
    ('North Beach', 'Presidio'): 17,
    ('North Beach', 'Chinatown'): 6,
    ('North Beach', 'Pacific Heights'): 8,
    ("Fisherman's Wharf", 'Bayview'): 26,
    ("Fisherman's Wharf", 'North Beach'): 6,
    ("Fisherman's Wharf", 'Haight-Ashbury'): 22,
    ("Fisherman's Wharf", 'Nob Hill'): 11,
    ("Fisherman's Wharf", 'Golden Gate Park'): 25,
    ("Fisherman's Wharf", 'Union Square'): 13,
    ("Fisherman's Wharf", 'Alamo Square'): 21,
    ("Fisherman's Wharf", 'Presidio'): 17,
    ("Fisherman's Wharf", 'Chinatown'): 12,
    ("Fisherman's Wharf", 'Pacific Heights'): 12,
    ('Haight-Ashbury', 'Bayview'): 18,
    ('Haight-Ashbury', 'North Beach'): 19,
    ('Haight-Ashbury', "Fisherman's Wharf"): 23,
    ('Haight-Ashbury', 'Nob Hill'): 15,
    ('Haight-Ashbury', 'Golden Gate Park'): 7,
    ('Haight-Ashbury', 'Union Square'): 19,
    ('Haight-Ashbury', 'Alamo Square'): 5,
    ('Haight-Ashbury', 'Presidio'): 15,
    ('Haight-Ashbury', 'Chinatown'): 19,
    ('Haight-Ashbury', 'Pacific Heights'): 12,
    ('Nob Hill', 'Bayview'): 19,
    ('Nob Hill', 'North Beach'): 8,
    ('Nob Hill', "Fisherman's Wharf"): 10,
    ('Nob Hill', 'Haight-Ashbury'): 13,
    ('Nob Hill', 'Golden Gate Park'): 17,
    ('Nob Hill', 'Union Square'): 7,
    ('Nob Hill', 'Alamo Square'): 11,
    ('Nob Hill', 'Presidio'): 17,
    ('Nob Hill', 'Chinatown'): 6,
    ('Nob Hill', 'Pacific Heights'): 8,
    ('Golden Gate Park', 'Bayview'): 23,
    ('Golden Gate Park', 'North Beach'): 23,
    ('Golden Gate Park', "Fisherman's Wharf"): 24,
    ('Golden Gate Park', 'Haight-Ashbury'): 7,
    ('Golden Gate Park', 'Nob Hill'): 20,
    ('Golden Gate Park', 'Union Square'): 22,
    ('Golden Gate Park', 'Alamo Square'): 9,
    ('Golden Gate Park', 'Presidio'): 11,
    ('Golden Gate Park', 'Chinatown'): 23,
    ('Golden Gate Park', 'Pacific Heights'): 16,
    ('Union Square', 'Bayview'): 15,
    ('Union Square', 'North Beach'): 10,
    ('Union Square', "Fisherman's Wharf"): 15,
    ('Union Square', 'Haight-Ashbury'): 18,
    ('Union Square', 'Nob Hill'): 9,
    ('Union Square', 'Golden Gate Park'): 22,
    ('Union Square', 'Alamo Square'): 15,
    ('Union Square', 'Presidio'): 24,
    ('Union Square', 'Chinatown'): 7,
    ('Union Square', 'Pacific Heights'): 15,
    ('Alamo Square', 'Bayview'): 16,
    ('Alamo Square', 'North Beach'): 15,
    ('Alamo Square', "Fisherman's Wharf"): 19,
    ('Alamo Square', 'Haight-Ashbury'): 5,
    ('Alamo Square', 'Nob Hill'): 11,
    ('Alamo Square', 'Golden Gate Park'): 9,
    ('Alamo Square', 'Union Square'): 14,
    ('Alamo Square', 'Presidio'): 17,
    ('Alamo Square', 'Chinatown'): 15,
    ('Alamo Square', 'Pacific Heights'): 10,
    ('Presidio', 'Bayview'): 31,
    ('Presidio', 'North Beach'): 18,
    ('Presidio', "Fisherman's Wharf"): 19,
    ('Presidio', 'Haight-Ashbury'): 15,
    ('Presidio', 'Nob Hill'): 18,
    ('Presidio', 'Golden Gate Park'): 12,
    ('Presidio', 'Union Square'): 22,
    ('Presidio', 'Alamo Square'): 19,
    ('Presidio', 'Chinatown'): 21,
    ('Presidio', 'Pacific Heights'): 11,
    ('Chinatown', 'Bayview'): 20,
    ('Chinatown', 'North Beach'): 3,
    ('Chinatown', "Fisherman's Wharf"): 8,
    ('Chinatown', 'Haight-Ashbury'): 19,
    ('Chinatown', 'Nob Hill'): 9,
    ('Chinatown', 'Golden Gate Park'): 23,
    ('Chinatown', 'Union Square'): 7,
    ('Chinatown', 'Alamo Square'): 17,
    ('Chinatown', 'Presidio'): 19,
    ('Chinatown', 'Pacific Heights'): 10,
    ('Pacific Heights', 'Bayview'): 22,
    ('Pacific Heights', 'North Beach'): 9,
    ('Pacific Heights', "Fisherman's Wharf"): 13,
    ('Pacific Heights', 'Haight-Ashbury'): 11,
    ('Pacific Heights', 'Nob Hill'): 8,
    ('Pacific Heights', 'Golden Gate Park'): 15,
    ('Pacific Heights', 'Union Square'): 12,
    ('Pacific Heights', 'Alamo Square'): 10,
    ('Pacific Heights', 'Presidio'): 11,
    ('Pacific Heights', 'Chinatown'): 11,
}

solver = Solver()

# Start must be met with fixed times
solver.add(friends[0]['met'] == True)
solver.add(friends[0]['start'] == 540)
solver.add(friends[0]['end'] == 540)

for friend in friends[1:]:
    met = friend['met']
    start = friend['start']
    end = friend['end']
    solver.add(Implies(met, start >= friend['available_start']))
    solver.add(Implies(met, end == start + friend['duration']))
    solver.add(Implies(met, end <= friend['available_end']))

# Add pairwise constraints including Start
for a, b in combinations(friends, 2):
    a_before_b = Bool(f"{a['name']}_before_{b['name']}")
    travel_ab = travel_time.get((a['location'], b['location']), None)
    travel_ba = travel_time.get((b['location'], a['location']), None)
    if travel_ab is None or travel_ba is None:
        continue
    solver.add(Implies(And(a['met'], b['met'], a_before_b), b['start'] >= a['end'] + travel_ab))
    solver.add(Implies(And(a['met'], b['met'], Not(a_before_b)), a['start'] >= b['end'] + travel_ba))

max_friends = Sum([If(f['met'], 1, 0) for f in friends[1:]])
solver.maximize(max_friends)

if solver.check() == sat:
    model = solver.model()
    schedule = []
    for friend in friends[1:]:
        if model.eval(friend['met']):
            start = model.eval(friend['start']).as_long()
            end = model.eval(friend['end']).as_long()
            schedule.append((friend['name'], start, end))
    schedule.sort(key=lambda x: x[1])
    print("Optimal Schedule:")
    for name, s, e in schedule:
        print(f"{name}: {s//60:02d}:{s%60:02d}-{e//60:02d}:{e%60:02d}")
else:
    print("No valid schedule found.")