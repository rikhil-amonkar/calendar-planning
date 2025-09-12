from z3 import *
import json

# Define friends with their meeting constraints
friends = [
    {
        'name': 'Joshua',
        'location': 'Embarcadero',
        'available_start': 585,  # 9:45 AM
        'available_end': 1080,   # 6:00 PM
        'min_duration': 105,
    },
    {
        'name': 'Jeffrey',
        'location': 'Bayview',
        'available_start': 585,  # 9:45 AM
        'available_end': 1215,   # 8:15 PM
        'min_duration': 75,
    },
    {
        'name': 'Charles',
        'location': 'Union Square',
        'available_start': 645,  # 10:45 AM
        'available_end': 1215,   # 8:15 PM
        'min_duration': 120,
    },
    {
        'name': 'Joseph',
        'location': 'Chinatown',
        'available_start': 420,  # 7:00 AM
        'available_end': 930,    # 3:30 PM
        'min_duration': 60,
    },
    {
        'name': 'Elizabeth',
        'location': 'Sunset District',
        'available_start': 540,  # 9:00 AM
        'available_end': 585,    # 9:45 AM
        'min_duration': 45,
    },
    {
        'name': 'Matthew',
        'location': 'Golden Gate Park',
        'available_start': 660,  # 11:00 AM
        'available_end': 1170,   # 7:30 PM
        'min_duration': 45,
    },
    {
        'name': 'Carol',
        'location': 'Financial District',
        'available_start': 645,  # 10:45 AM
        'available_end': 675,    # 11:15 AM
        'min_duration': 15,
    },
    {
        'name': 'Paul',
        'location': 'Haight-Ashbury',
        'available_start': 1155, # 7:15 PM
        'available_end': 1230,   # 8:30 PM
        'min_duration': 15,
    },
    {
        'name': 'Rebecca',
        'location': 'Mission District',
        'available_start': 1020, # 5:00 PM
        'available_end': 1305,   # 9:45 PM
        'min_duration': 45,
    },
]

# Define travel times between locations
travel_time = {
    'Marina District': {
        'Embarcadero': 14, 'Bayview': 27, 'Union Square': 16, 'Chinatown': 15,
        'Sunset District': 19, 'Golden Gate Park': 18, 'Financial District': 17,
        'Haight-Ashbury': 16, 'Mission District': 20
    },
    'Embarcadero': {
        'Marina District': 12, 'Bayview': 21, 'Union Square': 10, 'Chinatown': 7,
        'Sunset District': 30, 'Golden Gate Park': 25, 'Financial District': 5,
        'Haight-Ashbury': 21, 'Mission District': 20
    },
    'Bayview': {
        'Marina District': 27, 'Embarcadero': 19, 'Union Square': 18, 'Chinatown': 19,
        'Sunset District': 23, 'Golden Gate Park': 22, 'Financial District': 19,
        'Haight-Ashbury': 19, 'Mission District': 13
    },
    'Union Square': {
        'Marina District': 18, 'Embarcadero': 11, 'Bayview': 15, 'Chinatown': 7,
        'Sunset District': 27, 'Golden Gate Park': 22, 'Financial District': 9,
        'Haight-Ashbury': 18, 'Mission District': 14
    },
    'Chinatown': {
        'Marina District': 12, 'Embarcadero': 5, 'Bayview': 20, 'Union Square': 7,
        'Sunset District': 29, 'Golden Gate Park': 23, 'Financial District': 5,
        'Haight-Ashbury': 19, 'Mission District': 17
    },
    'Sunset District': {
        'Marina District': 21, 'Embarcadero': 30, 'Bayview': 22, 'Union Square': 30,
        'Chinatown': 30, 'Golden Gate Park': 11, 'Financial District': 30,
        'Haight-Ashbury': 15, 'Mission District': 25
    },
    'Golden Gate Park': {
        'Marina District': 16, 'Embarcadero': 25, 'Bayview': 23, 'Union Square': 22,
        'Chinatown': 23, 'Sunset District': 10, 'Financial District': 26,
        'Haight-Ashbury': 7, 'Mission District': 17
    },
    'Financial District': {
        'Marina District': 15, 'Embarcadero': 4, 'Bayview': 19, 'Union Square': 9,
        'Chinatown': 5, 'Sunset District': 30, 'Golden Gate Park': 23,
        'Haight-Ashbury': 19, 'Mission District': 17
    },
    'Haight-Ashbury': {
        'Marina District': 17, 'Embarcadero': 20, 'Bayview': 18, 'Union Square': 19,
        'Chinatown': 19, 'Sunset District': 15, 'Golden Gate Park': 7,
        'Financial District': 21, 'Mission District': 11
    },
    'Mission District': {
        'Marina District': 19, 'Embarcadero': 19, 'Bayview': 14, 'Union Square': 15,
        'Chinatown': 16, 'Sunset District': 24, 'Golden Gate Park': 17,
        'Financial District': 15, 'Haight-Ashbury': 12
    },
}

# Z3 setup
n = len(friends)
meet = [Bool(f'meet_{i}') for i in range(n)]
start = [Int(f'start_{i}') for i in range(n)]
order = [Int(f'order_{i}') for i in range(n)]

opt = Optimize()

# Add constraints for each friend
for i in range(n):
    friend = friends[i]
    loc_i = friend['location']
    as_i = friend['available_start']
    ae_i = friend['available_end']
    min_d_i = friend['min_duration']
    
    # If met, start is within available time and has enough duration
    opt.add(Implies(meet[i], And(start[i] >= as_i, start[i] + min_d_i <= ae_i)))
    
    # If met and order is 1, start >= arrival time from Marina District
    arrival_time_first = 540 + travel_time['Marina District'][loc_i]
    opt.add(Implies(And(meet[i], order[i] == 1), start[i] >= arrival_time_first))
    
# Add constraints for order uniqueness and ordering between friends
for i in range(n):
    for j in range(n):
        if i == j:
            continue
        loc_i = friends[i]['location']
        loc_j = friends[j]['location']
        tt = travel_time[loc_i][loc_j]
        min_d_i = friends[i]['min_duration']
        # If meet[i] and meet[j] and order[i] < order[j], then start[j] >= start[i] + min_d_i + tt
        opt.add(Implies(And(meet[i], meet[j], order[i] < order[j]), start[j] >= start[i] + min_d_i + tt))

# Ensure order variables are positive integers if met
for i in range(n):
    opt.add(Implies(meet[i], order[i] >= 1))

# Ensure orders are unique for met friends
for i in range(n):
    for j in range(i+1, n):
        opt.add(Implies(And(meet[i], meet[j]), order[i] != order[j]))

# Maximize the number of friends met
opt.maximize(Sum([If(meet[i], 1, 0) for i in range(n)]))

# Check if the problem is satisfiable
if opt.check() == sat:
    model = opt.model()
    
    # Extract met friends and their data
    met_indices = [i for i in range(n) if is_true(model.eval(meet[i]))]
    met_data = []
    for i in met_indices:
        start_val = model.eval(start[i]).as_long()
        end_val = start_val + friends[i]['min_duration']
        order_val = model.eval(order[i]).as_long()
        met_data.append( (order_val, i, start_val, end_val) )
    
    # Sort by order
    met_data.sort()
    
    # Build the itinerary
    itinerary = []
    for order_val, i, start_val, end_val in met_data:
        friend = friends[i]
        # Convert start and end to H:MM format
        def to_time_str(minutes):
            h = minutes // 60
            m = minutes % 60
            return f"{h}:{m:02d}"
        start_str = to_time_str(start_val)
        end_str = to_time_str(end_val)
        itinerary.append({
            "action": "meet",
            "location": friend['location'],
            "person": friend['name'],
            "start_time": start_str,
            "end_time": end_str
        })
    
    # Output JSON
    result = {"itinerary": itinerary}
    print(json.dumps(result, indent=2))
else:
    print(json.dumps({"itinerary": []}))