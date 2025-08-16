import itertools
import json
from z3 import *

# Define friends and their constraints
friends = [
    {
        'name': 'Margaret',
        'location': 'Bayview',
        'available_start': 9 * 60 + 30,  # 9:30 AM
        'available_end': 13 * 60 + 30,   # 1:30 PM
        'required_duration': 30
    },
    {
        'name': 'Robert',
        'location': 'Chinatown',
        'available_start': 12 * 60 + 15,  # 12:15 PM
        'available_end': 20 * 60 + 15,   # 8:15 PM
        'required_duration': 15
    },
    {
        'name': 'Kimberly',
        'location': 'Marina District',
        'available_start': 13 * 60 + 15,  # 1:15 PM
        'available_end': 16 * 60 + 45,   # 4:45 PM
        'required_duration': 15
    },
    {
        'name': 'Rebecca',
        'location': 'Financial District',
        'available_start': 13 * 60 + 15,  # 1:15 PM
        'available_end': 16 * 60 + 45,   # 4:45 PM
        'required_duration': 75
    },
    {
        'name': 'Kenneth',
        'location': 'Union Square',
        'available_start': 19 * 60 + 30,  # 7:30 PM
        'available_end': 21 * 60 + 15,   # 9:15 PM
        'required_duration': 75
    }
]

# Define travel times between locations
travel_times = {
    ('Richmond District', 'Marina District'): 9,
    ('Richmond District', 'Chinatown'): 20,
    ('Richmond District', 'Financial District'): 22,
    ('Richmond District', 'Bayview'): 26,
    ('Richmond District', 'Union Square'): 21,
    ('Marina District', 'Richmond District'): 11,
    ('Marina District', 'Chinatown'): 16,
    ('Marina District', 'Financial District'): 17,
    ('Marina District', 'Bayview'): 27,
    ('Marina District', 'Union Square'): 16,
    ('Chinatown', 'Richmond District'): 20,
    ('Chinatown', 'Marina District'): 12,
    ('Chinatown', 'Financial District'): 5,
    ('Chinatown', 'Bayview'): 22,
    ('Chinatown', 'Union Square'): 7,
    ('Financial District', 'Richmond District'): 21,
    ('Financial District', 'Marina District'): 15,
    ('Financial District', 'Chinatown'): 5,
    ('Financial District', 'Bayview'): 19,
    ('Financial District', 'Union Square'): 9,
    ('Bayview', 'Richmond District'): 25,
    ('Bayview', 'Marina District'): 25,
    ('Bayview', 'Chinatown'): 18,
    ('Bayview', 'Financial District'): 19,
    ('Bayview', 'Union Square'): 17,
    ('Union Square', 'Richmond District'): 20,
    ('Union Square', 'Marina District'): 18,
    ('Union Square', 'Chinatown'): 7,
    ('Union Square', 'Financial District'): 9,
    ('Union Square', 'Bayview'): 15,
}

# Try all permutations of friends to find a feasible schedule
for perm in itertools.permutations(friends):
    s = Solver()
    starts = []
    ends = []
    for friend in perm:
        start = Int(f"{friend['name']}_start")
        end = Int(f"{friend['name']}_end")
        starts.append(start)
        ends.append(end)
        s.add(end == start + friend['required_duration'])
        s.add(start >= friend['available_start'])
        s.add(end <= friend['available_end'])
    
    current_time = 540  # 9:00 AM
    current_location = 'Richmond District'
    for i in range(len(perm)):
        friend = perm[i]
        next_location = friend['location']
        travel_time = travel_times.get((current_location, next_location), None)
        if travel_time is None:
            continue
        arrival_time = current_time + travel_time
        s.add(starts[i] >= arrival_time)
        current_time = ends[i]
        current_location = next_location
    
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for i in range(len(perm)):
            friend = perm[i]
            start_val = model[starts[i]].as_long()
            end_val = model[ends[i]].as_long()
            start_time = f"{(start_val // 60):02d}:{(start_val % 60):02d}"
            end_time = f"{(end_val // 60):02d}:{(end_val % 60):02d}"
            itinerary.append({
                "action": "meet",
                "person": friend['name'],
                "start_time": start_time,
                "end_time": end_time
            })
        print(json.dumps({"itinerary": itinerary}))
        exit()