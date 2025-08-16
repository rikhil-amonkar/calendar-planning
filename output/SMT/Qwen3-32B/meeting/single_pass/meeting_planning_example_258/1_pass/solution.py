import itertools
import json
from z3 import *

def format_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h:02d}:{m:02d}"

friends = [
    {
        'name': 'Barbara',
        'location': "Fisherman's Wharf",
        'available_start': 9*60 + 15,  # 9:15 AM
        'available_end': 20*60 + 15,   # 8:15 PM
        'min_duration': 120
    },
    {
        'name': 'Betty',
        'location': 'Presidio',
        'available_start': 10*60 + 15, # 10:15 AM
        'available_end': 21*60 + 30,   # 9:30 PM
        'min_duration': 45
    },
    {
        'name': 'David',
        'location': 'Richmond District',
        'available_start': 13*60,      # 1:00 PM
        'available_end': 20*60 + 15,   # 8:15 PM
        'min_duration': 90
    }
]

travel_time = {
    ('Embarcadero', "Fisherman's Wharf"): 6,
    ("Fisherman's Wharf", 'Embarcadero'): 8,
    ('Embarcadero', 'Presidio'): 20,
    ('Presidio', 'Embarcadero'): 20,
    ('Embarcadero', 'Richmond District'): 21,
    ('Richmond District', 'Embarcadero'): 19,
    ('Presidio', "Fisherman's Wharf"): 19,
    ("Fisherman's Wharf", 'Presidio'): 17,
    ('Presidio', 'Richmond District'): 7,
    ('Richmond District', 'Presidio'): 7,
    ("Fisherman's Wharf", 'Richmond District'): 18,
    ('Richmond District', "Fisherman's Wharf"): 18,
}

for perm in itertools.permutations(friends):
    s = Solver()
    starts = [Int(f"{f['name']}_start") for f in perm]
    ends = [Int(f"{f['name']}_end") for f in perm]
    current_time = 9 * 60  # 9:00 AM in minutes
    current_location = 'Embarcadero'
    for i in range(len(perm)):
        friend = perm[i]
        from_loc = current_location
        to_loc = friend['location']
        travel = travel_time[(from_loc, to_loc)]
        arrival_time = current_time + travel
        # Add constraints for start time
        s.add(starts[i] >= arrival_time)
        s.add(starts[i] >= friend['available_start'])
        # End time is start + duration
        s.add(ends[i] == starts[i] + friend['min_duration'])
        # End time must be within friend's available time
        s.add(ends[i] <= friend['available_end'])
        # Update current_time and current_location for next iteration
        current_time = ends[i]
        current_location = to_loc
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for i in range(len(perm)):
            friend = perm[i]
            start = model[starts[i]].as_long()
            end = model[ends[i]].as_long()
            start_time = format_time(start)
            end_time = format_time(end)
            itinerary.append({
                "action": "meet",
                "person": friend['name'],
                "start_time": start_time,
                "end_time": end_time
            })
        print("SOLUTION:")
        print(json.dumps({"itinerary": itinerary}))
        exit()