import itertools
import json

def format_time(minutes):
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

friends = [
    {
        'location': 'Embarcadero',
        'name': 'Jessica',
        'start': 1125,  # 4:45 PM
        'end': 1200,    # 7:00 PM
        'duration': 30
    },
    {
        'location': 'Richmond District',
        'name': 'Sandra',
        'start': 1170,  # 6:30 PM
        'end': 1385,    # 9:45 PM
        'duration': 120
    },
    {
        'location': 'Fisherman\'s Wharf',
        'name': 'Jason',
        'start': 960,    # 4:00 PM
        'end': 1125,    # 4:45 PM
        'duration': 30
    }
]

for perm in itertools.permutations(friends):
    current_time = 540  # 9:00 AM
    current_location = 'Bayview'
    itinerary = []
    valid = True
    
    for friend in perm:
        travel = travel_times.get((current_location, friend['location']), None)
        if travel is None:
            valid = False
            break
        arrival = current_time + travel
        meeting_start = max(arrival, friend['start'])
        meeting_end = meeting_start + friend['duration']
        if meeting_end > friend['end']:
            valid = False
            break
        itinerary.append({
            'action': 'meet',
            'location': friend['location'],
            'person': friend['name'],
            'start_time': format_time(meeting_start),
            'end_time': format_time(meeting_end)
        })
        current_time = meeting_end
        current_location = friend['location']
    
    if valid:
        print(json.dumps({'itinerary': itinerary}))
        exit()

# If no permutation meets all three, check for permutations with two friends
max_meetings = 0
best_itinerary = []
for r in range(2, 0, -1):
    for perm in itertools.permutations(friends, r):
        current_time = 540
        current_location = 'Bayview'
        itinerary = []
        valid = True
        
        for friend in perm:
            travel = travel_times.get((current_location, friend['location']), None)
            if travel is None:
                valid = False
                break
            arrival = current_time + travel
            meeting_start = max(arrival, friend['start'])
            meeting_end = meeting_start + friend['duration']
            if meeting_end > friend['end']:
                valid = False
                break
            itinerary.append({
                'action': 'meet',
                'location': friend['location'],
                'person': friend['name'],
                'start_time': format_time(meeting_start),
                'end_time': format_time(meeting_end)
            })
            current_time = meeting_end
            current_location = friend['location']
        
        if valid and len(itinerary) > max_meetings:
            max_meetings = len(itinerary)
            best_itinerary = itinerary
            if max_meetings == 2:
                print(json.dumps({'itinerary': best_itinerary}))
                exit()

print(json.dumps({'itinerary': best_itinerary}))