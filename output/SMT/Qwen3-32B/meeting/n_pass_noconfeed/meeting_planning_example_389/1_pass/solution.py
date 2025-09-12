import itertools
import json
from z3 import *

def format_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

friends = [
    {
        'name': 'Sarah',
        'location': "Fisherman's Wharf",
        'available_start': 14*60 + 45,  # 885
        'available_end': 17*60 + 30,    # 1050
        'required_duration': 105
    },
    {
        'name': 'Mary',
        'location': 'Richmond District',
        'available_start': 13*60 + 0,   # 780
        'available_end': 19*60 + 15,    # 1155
        'required_duration': 75
    },
    {
        'name': 'Helen',
        'location': 'Mission District',
        'available_start': 21*60 + 45,  # 1305
        'available_end': 22*60 + 30,    # 1350
        'required_duration': 30
    },
    {
        'name': 'Thomas',
        'location': 'Bayview',
        'available_start': 15*60 + 15,  # 915
        'available_end': 18*60 + 45,    # 1125
        'required_duration': 120
    }
]

travel_times = {
    ('Haight-Ashbury', "Fisherman's Wharf"): 23,
    ("Fisherman's Wharf", 'Haight-Ashbury'): 22,
    ('Haight-Ashbury', 'Richmond District'): 10,
    ('Richmond District', 'Haight-Ashbury'): 10,
    ('Haight-Ashbury', 'Mission District'): 11,
    ('Mission District', 'Haight-Ashbury'): 12,
    ('Haight-Ashbury', 'Bayview'): 18,
    ('Bayview', 'Haight-Ashbury'): 19,
    ("Fisherman's Wharf", 'Richmond District'): 18,
    ('Richmond District', "Fisherman's Wharf"): 18,
    ("Fisherman's Wharf", 'Mission District'): 22,
    ('Mission District', "Fisherman's Wharf"): 22,
    ("Fisherman's Wharf", 'Bayview'): 26,
    ('Bayview', "Fisherman's Wharf"): 25,
    ('Richmond District', 'Mission District'): 20,
    ('Mission District', 'Richmond District'): 20,
    ('Richmond District', 'Bayview'): 26,
    ('Bayview', 'Richmond District'): 25,
    ('Mission District', 'Bayview'): 15,
    ('Bayview', 'Mission District'): 13,
}

for size in range(4, 0, -1):
    for perm in itertools.permutations(friends, size):
        solver = Solver()
        start_vars = [Int(f"start_{i}") for i in range(size)]
        prev_time = 540  # 9:00 AM in minutes
        prev_location = 'Haight-Ashbury'
        for i in range(size):
            friend = perm[i]
            loc = friend['location']
            travel_time = travel_times[(prev_location, loc)]
            arrival_time = prev_time + travel_time
            available_start = friend['available_start']
            available_end = friend['available_end']
            duration = friend['required_duration']
            s = start_vars[i]
            # Ensure start time is after arrival and available start
            solver.add(And(s >= arrival_time, s >= available_start))
            # Ensure meeting ends before available end
            solver.add(s + duration <= available_end)
            prev_time = s + duration
            prev_location = loc
        if solver.check() == sat:
            model = solver.model()
            itinerary = []
            for i in range(size):
                friend = perm[i]
                s_val = model[start_vars[i]].as_long()
                e_val = s_val + friend['required_duration']
                itinerary.append({
                    'action': 'meet',
                    'location': friend['location'],
                    'person': friend['name'],
                    'start_time': format_time(s_val),
                    'end_time': format_time(e_val)
                })
            print(json.dumps({'itinerary': itinerary}))
            exit()

print(json.dumps({'itinerary': []}))