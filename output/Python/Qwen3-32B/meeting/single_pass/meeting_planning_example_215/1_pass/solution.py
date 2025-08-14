import itertools
import json

def to_time_str(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

travel_times = {
    ('Bayview', 'Embarcadero'): 19,
    ('Bayview', 'Richmond District'): 25,
    ('Bayview', 'Fisherman\'s Wharf'): 25,
    ('Embarcadero', 'Bayview'): 21,
    ('Embarcadero', 'Richmond District'): 21,
    ('Embarcadero', 'Fisherman\'s Wharf'): 6,
    ('Richmond District', 'Bayview'): 26,
    ('Richmond District', 'Embarcadero'): 19,
    ('Richmond District', 'Fisherman\'s Wharf'): 18,
    ('Fisherman\'s Wharf', 'Bayview'): 26,
    ('Fisherman\'s Wharf', 'Embarcadero'): 8,
    ('Fisherman\'s Wharf', 'Richmond District'): 18,
}

def get_travel_time(from_loc, to_loc):
    return travel_times.get((from_loc, to_loc), float('inf'))

friends = [
    {
        'name': 'Jason',
        'location': "Fisherman's Wharf",
        'available_start': 16 * 60,  # 4:00 PM
        'available_end': 16 * 60 + 45,  # 4:45 PM
        'duration': 30
    },
    {
        'name': 'Jessica',
        'location': 'Embarcadero',
        'available_start': 16 * 60 + 45,  # 4:45 PM
        'available_end': 19 * 60,  # 7:00 PM
        'duration': 30
    },
    {
        'name': 'Sandra',
        'location': 'Richmond District',
        'available_start': 18 * 60 + 30,  # 6:30 PM
        'available_end': 21 * 60 + 45,  # 9:45 PM
        'duration': 120
    }
]

best_schedule = None
max_met = 0
earliest_end = float('inf')

for r in range(1, 4):  # lengths 1, 2, 3
    for perm in itertools.permutations(friends, r):
        current_time = 9 * 60  # 9:00 AM in minutes
        current_location = 'Bayview'
        valid = True
        itinerary = []
        for friend in perm:
            travel_time = get_travel_time(current_location, friend['location'])
            arrival_time = current_time + travel_time
            if arrival_time > friend['available_end']:
                valid = False
                break
            start_time = max(arrival_time, friend['available_start'])
            if start_time + friend['duration'] > friend['available_end']:
                valid = False
                break
            end_time = start_time + friend['duration']
            itinerary.append({
                'action': 'meet',
                'location': friend['location'],
                'person': friend['name'],
                'start_time': start_time,
                'end_time': end_time
            })
            current_time = end_time
            current_location = friend['location']
        if valid:
            num_met = len(perm)
            if num_met > max_met or (num_met == max_met and current_time < earliest_end):
                max_met = num_met
                earliest_end = current_time
                best_schedule = itinerary

if best_schedule:
    result = {
        "itinerary": [
            {
                "action": "meet",
                "location": entry["location"],
                "person": entry["person"],
                "start_time": to_time_str(entry["start_time"]),
                "end_time": to_time_str(entry["end_time"]),
            }
            for entry in best_schedule
        ]
    }
    print(json.dumps(result, indent=2))
else:
    print(json.dumps({"itinerary": []}))