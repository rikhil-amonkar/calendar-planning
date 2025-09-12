from z3 import *
import json

# Define friends
friends = [
    {
        'name': 'Paul',
        'location': 'Nob Hill',
        'available_start': 16 * 60 + 15,  # 4:15 PM
        'available_end': 21 * 60 + 15,    # 9:15 PM
        'min_duration': 60
    },
    {
        'name': 'Carol',
        'location': 'Union Square',
        'available_start': 18 * 60,       # 6:00 PM
        'available_end': 20 * 60 + 15,    # 8:15 PM
        'min_duration': 120
    },
    {
        'name': 'Patricia',
        'location': 'Chinatown',
        'available_start': 20 * 60,       # 8:00 PM
        'available_end': 21 * 60 + 30,    # 9:30 PM
        'min_duration': 75
    },
    {
        'name': 'Karen',
        'location': 'The Castro',
        'available_start': 17 * 60,       # 5:00 PM
        'available_end': 19 * 60,         # 7:00 PM
        'min_duration': 45
    },
    {
        'name': 'Nancy',
        'location': 'Presidio',
        'available_start': 11 * 60 + 45,  # 11:45 AM
        'available_end': 22 * 60,         # 10:00 PM
        'min_duration': 30
    },
    {
        'name': 'Jeffrey',
        'location': 'Pacific Heights',
        'available_start': 20 * 60,       # 8:00 PM
        'available_end': 20 * 60 + 45,    # 8:45 PM
        'min_duration': 45
    },
    {
        'name': 'Matthew',
        'location': 'Russian Hill',
        'available_start': 15 * 60 + 45,  # 3:45 PM
        'available_end': 21 * 60 + 45,    # 9:45 PM
        'min_duration': 75
    },
]

# Define travel times
travel_times = {
    # From Bayview
    ('Bayview', 'Nob Hill'): 20,
    ('Bayview', 'Union Square'): 17,
    ('Bayview', 'Chinatown'): 18,
    ('Bayview', 'The Castro'): 20,
    ('Bayview', 'Presidio'): 31,
    ('Bayview', 'Pacific Heights'): 23,
    ('Bayview', 'Russian Hill'): 23,
    # From Nob Hill
    ('Nob Hill', 'Bayview'): 19,
    ('Nob Hill', 'Union Square'): 7,
    ('Nob Hill', 'Chinatown'): 6,
    ('Nob Hill', 'The Castro'): 17,
    ('Nob Hill', 'Presidio'): 17,
    ('Nob Hill', 'Pacific Heights'): 8,
    ('Nob Hill', 'Russian Hill'): 5,
    # From Union Square
    ('Union Square', 'Bayview'): 15,
    ('Union Square', 'Nob Hill'): 9,
    ('Union Square', 'Chinatown'): 7,
    ('Union Square', 'The Castro'): 19,
    ('Union Square', 'Presidio'): 24,
    ('Union Square', 'Pacific Heights'): 15,
    ('Union Square', 'Russian Hill'): 13,
    # From Chinatown
    ('Chinatown', 'Bayview'): 22,
    ('Chinatown', 'Nob Hill'): 8,
    ('Chinatown', 'Union Square'): 7,
    ('Chinatown', 'The Castro'): 22,
    ('Chinatown', 'Presidio'): 19,
    ('Chinatown', 'Pacific Heights'): 10,
    ('Chinatown', 'Russian Hill'): 7,
    # From The Castro
    ('The Castro', 'Bayview'): 19,
    ('The Castro', 'Nob Hill'): 16,
    ('The Castro', 'Union Square'): 19,
    ('The Castro', 'Chinatown'): 20,
    ('The Castro', 'Presidio'): 20,
    ('The Castro', 'Pacific Heights'): 16,
    ('The Castro', 'Russian Hill'): 18,
    # From Presidio
    ('Presidio', 'Bayview'): 31,
    ('Presidio', 'Nob Hill'): 18,
    ('Presidio', 'Union Square'): 22,
    ('Presidio', 'Chinatown'): 21,
    ('Presidio', 'The Castro'): 21,
    ('Presidio', 'Pacific Heights'): 11,
    ('Presidio', 'Russian Hill'): 14,
    # From Pacific Heights
    ('Pacific Heights', 'Bayview'): 22,
    ('Pacific Heights', 'Nob Hill'): 8,
    ('Pacific Heights', 'Union Square'): 12,
    ('Pacific Heights', 'Chinatown'): 11,
    ('Pacific Heights', 'The Castro'): 16,
    ('Pacific Heights', 'Presidio'): 11,
    ('Pacific Heights', 'Russian Hill'): 7,
    # From Russian Hill
    ('Russian Hill', 'Bayview'): 23,
    ('Russian Hill', 'Nob Hill'): 5,
    ('Russian Hill', 'Union Square'): 11,
    ('Russian Hill', 'Chinatown'): 9,
    ('Russian Hill', 'The Castro'): 21,
    ('Russian Hill', 'Presidio'): 14,
    ('Russian Hill', 'Pacific Heights'): 7,
}

# Create Z3 solver
opt = Optimize()

include_vars = []
start_vars = []

# Create variables for each friend
for f in friends:
    include = Bool(f"include_{f['name']}")
    start = Int(f"start_{f['name']}")
    include_vars.append(include)
    start_vars.append(start)

# Add constraints for each friend
for i, f in enumerate(friends):
    include = include_vars[i]
    start = start_vars[i]
    loc = f['location']
    # Constraint: if included, start >= available_start
    opt.add(Implies(include, start >= f['available_start']))
    # Constraint: if included, start + duration <= available_end
    opt.add(Implies(include, start + f['min_duration'] <= f['available_end']))
    # Constraint: if included, start >= initial_time + travel time from Bayview
    travel_time_initial = travel_times[('Bayview', loc)]
    opt.add(Implies(include, start >= 540 + travel_time_initial))

# Add pairwise constraints between friends
for i in range(len(friends)):
    for j in range(i + 1, len(friends)):
        f1 = friends[i]
        f2 = friends[j]
        include1 = include_vars[i]
        include2 = include_vars[j]
        start1 = start_vars[i]
        start2 = start_vars[j]
        loc1 = f1['location']
        loc2 = f2['location']
        travel_time12 = travel_times[(loc1, loc2)]
        travel_time21 = travel_times[(loc2, loc1)]
        duration1 = f1['min_duration']
        duration2 = f2['min_duration']
        # Add constraint for the pair
        opt.add(Implies(And(include1, include2), Or(
            start1 + duration1 + travel_time12 <= start2,
            start2 + duration2 + travel_time21 <= start1
        )))

# Maximize the number of included friends
sum_include = Sum([If(include, 1, 0) for include in include_vars])
opt.maximize(sum_include)

# Check for solution
if opt.check() == sat:
    model = opt.model()
    # Extract included friends and their start times
    included = []
    for i in range(len(friends)):
        if is_true(model.eval(include_vars[i])):
            start_val = model.eval(start_vars[i]).as_long()
            included.append((friends[i], start_val))
    # Sort by start time
    included.sort(key=lambda x: x[1])
    # Generate itinerary
    itinerary = []
    for f, start_time in included:
        end_time = start_time + f['min_duration']
        start_str = f"{start_time // 60}:{start_time % 60:02d}"
        end_str = f"{end_time // 60}:{end_time % 60:02d}"
        itinerary.append({
            "action": "meet",
            "location": f['location'],
            "person": f['name'],
            "start_time": start_str,
            "end_time": end_str
        })
    # Output JSON
    print(json.dumps({"itinerary": itinerary}, indent=2))
else:
    print("No solution found")