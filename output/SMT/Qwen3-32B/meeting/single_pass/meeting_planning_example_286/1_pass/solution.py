import itertools
from z3 import *
import json

friends_data = {
    'Carol': {
        'location': 'Sunset District',
        'available_start': 10 * 60 + 15,  # 615
        'available_end': 11 * 60 + 45,    # 705
        'required_duration': 30
    },
    'Karen': {
        'location': 'Bayview',
        'available_start': 12 * 60 + 45,  # 765
        'available_end': 15 * 60 + 0,     # 900
        'required_duration': 120
    },
    'Rebecca': {
        'location': 'Mission District',
        'available_start': 11 * 60 + 30,  # 690
        'available_end': 20 * 60 + 15,    # 1215
        'required_duration': 120
    }
}

travel_time = {
    # from, to : time in minutes
    ('Union Square', 'Mission District'): 14,
    ('Union Square', 'Bayview'): 15,
    ('Union Square', 'Sunset District'): 26,
    ('Mission District', 'Union Square'): 15,
    ('Mission District', 'Bayview'): 15,
    ('Mission District', 'Sunset District'): 24,
    ('Bayview', 'Union Square'): 17,
    ('Bayview', 'Mission District'): 13,
    ('Bayview', 'Sunset District'): 23,
    ('Sunset District', 'Union Square'): 30,
    ('Sunset District', 'Mission District'): 24,
    ('Sunset District', 'Bayview'): 22,
}

def to_time_str(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

friends = ['Carol', 'Karen', 'Rebecca']

for perm in itertools.permutations(friends):
    s = Solver()
    starts = [Int(f'start_{friend}') for friend in perm]
    ends = [Int(f'end_{friend}') for friend in perm]
    
    current_time = 540  # 9:00 AM in minutes
    current_location = 'Union Square'
    
    for i in range(len(perm)):
        friend = perm[i]
        friend_location = friends_data[friend]['location']
        available_start = friends_data[friend]['available_start']
        available_end = friends_data[friend]['available_end']
        required_duration = friends_data[friend]['required_duration']
        
        # Compute arrival_time
        travel_time_val = travel_time.get((current_location, friend_location), 0)
        arrival_time = current_time + travel_time_val
        
        # Add constraints
        s.add(starts[i] >= If(arrival_time >= available_start, arrival_time, available_start))
        s.add(ends[i] >= starts[i] + required_duration)
        s.add(ends[i] <= available_end)
        
        # Update current_time and current_location
        current_time = ends[i]
        current_location = friend_location
    
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for i in range(len(perm)):
            friend = perm[i]
            start_time = model.evaluate(starts[i]).as_long()
            end_time = model.evaluate(ends[i]).as_long()
            start_str = to_time_str(start_time)
            end_str = to_time_str(end_time)
            itinerary.append({
                "action": "meet",
                "person": friend,
                "start_time": start_str,
                "end_time": end_str
            })
        # Output the solution
        print("SOLUTION:")
        print(json.dumps({"itinerary": itinerary}))
        exit()

# If no permutation is found, return empty?
print("SOLUTION:")
print(json.dumps({"itinerary": []}))