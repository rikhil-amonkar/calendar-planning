import itertools
import json

travel_times = {
    ('Marina District', 'Richmond District'): 11,
    ('Marina District', 'Union Square'): 16,
    ('Marina District', 'Nob Hill'): 12,
    ('Marina District', 'Fisherman\'s Wharf'): 10,
    ('Marina District', 'Golden Gate Park'): 18,
    ('Marina District', 'Embarcadero'): 14,
    ('Marina District', 'Financial District'): 17,
    ('Marina District', 'North Beach'): 11,
    ('Marina District', 'Presidio'): 10,
    ('Richmond District', 'Marina District'): 9,
    ('Richmond District', 'Union Square'): 21,
    ('Richmond District', 'Nob Hill'): 17,
    ('Richmond District', 'Fisherman\'s Wharf'): 18,
    ('Richmond District', 'Golden Gate Park'): 9,
    ('Richmond District', 'Embarcadero'): 19,
    ('Richmond District', 'Financial District'): 22,
    ('Richmond District', 'North Beach'): 17,
    ('Richmond District', 'Presidio'): 7,
    ('Union Square', 'Marina District'): 18,
    ('Union Square', 'Richmond District'): 20,
    ('Union Square', 'Nob Hill'): 9,
    ('Union Square', 'Fisherman\'s Wharf'): 15,
    ('Union Square', 'Golden Gate Park'): 22,
    ('Union Square', 'Embarcadero'): 11,
    ('Union Square', 'Financial District'): 9,
    ('Union Square', 'North Beach'): 10,
    ('Union Square', 'Presidio'): 24,
    ('Nob Hill', 'Marina District'): 11,
    ('Nob Hill', 'Richmond District'): 14,
    ('Nob Hill', 'Union Square'): 7,
    ('Nob Hill', 'Fisherman\'s Wharf'): 10,
    ('Nob Hill', 'Golden Gate Park'): 17,
    ('Nob Hill', 'Embarcadero'): 9,
    ('Nob Hill', 'Financial District'): 9,
    ('Nob Hill', 'North Beach'): 8,
    ('Nob Hill', 'Presidio'): 17,
    ('Fisherman\'s Wharf', 'Marina District'): 9,
    ('Fisherman\'s Wharf', 'Richmond District'): 18,
    ('Fisherman\'s Wharf', 'Union Square'): 13,
    ('Fisherman\'s Wharf', 'Nob Hill'): 11,
    ('Fisherman\'s Wharf', 'Golden Gate Park'): 25,
    ('Fisherman\'s Wharf', 'Embarcadero'): 8,
    ('Fisherman\'s Wharf', 'Financial District'): 11,
    ('Fisherman\'s Wharf', 'North Beach'): 6,
    ('Fisherman\'s Wharf', 'Presidio'): 17,
    ('Golden Gate Park', 'Marina District'): 16,
    ('Golden Gate Park', 'Richmond District'): 7,
    ('Golden Gate Park', 'Union Square'): 22,
    ('Golden Gate Park', 'Nob Hill'): 20,
    ('Golden Gate Park', 'Fisherman\'s Wharf'): 24,
    ('Golden Gate Park', 'Embarcadero'): 25,
    ('Golden Gate Park', 'Financial District'): 26,
    ('Golden Gate Park', 'North Beach'): 23,
    ('Golden Gate Park', 'Presidio'): 11,
    ('Embarcadero', 'Marina District'): 12,
    ('Embarcadero', 'Richmond District'): 21,
    ('Embarcadero', 'Union Square'): 10,
    ('Embarcadero', 'Nob Hill'): 10,
    ('Embarcadero', 'Fisherman\'s Wharf'): 6,
    ('Embarcadero', 'Golden Gate Park'): 25,
    ('Embarcadero', 'Financial District'): 5,
    ('Embarcadero', 'North Beach'): 5,
    ('Embarcadero', 'Presidio'): 20,
    ('Financial District', 'Marina District'): 15,
    ('Financial District', 'Richmond District'): 21,
    ('Financial District', 'Union Square'): 9,
    ('Financial District', 'Nob Hill'): 8,
    ('Financial District', 'Fisherman\'s Wharf'): 10,
    ('Financial District', 'Golden Gate Park'): 23,
    ('Financial District', 'Embarcadero'): 4,
    ('Financial District', 'North Beach'): 7,
    ('Financial District', 'Presidio'): 22,
    ('North Beach', 'Marina District'): 9,
    ('North Beach', 'Richmond District'): 18,
    ('North Beach', 'Union Square'): 7,
    ('North Beach', 'Nob Hill'): 7,
    ('North Beach', 'Fisherman\'s Wharf'): 5,
    ('North Beach', 'Golden Gate Park'): 22,
    ('North Beach', 'Embarcadero'): 6,
    ('North Beach', 'Financial District'): 8,
    ('North Beach', 'Presidio'): 17,
    ('Presidio', 'Marina District'): 11,
    ('Presidio', 'Richmond District'): 7,
    ('Presidio', 'Union Square'): 22,
    ('Presidio', 'Nob Hill'): 18,
    ('Presidio', 'Fisherman\'s Wharf'): 19,
    ('Presidio', 'Golden Gate Park'): 12,
    ('Presidio', 'Embarcadero'): 20,
    ('Presidio', 'Financial District'): 23,
    ('Presidio', 'North Beach'): 18,
}

friends = [
    {
        'name': 'Stephanie',
        'location': 'Richmond District',
        'start': 1020 - 45,  # 16:15 (4:15 PM) converted to minutes since midnight
        'end': 1410,        # 23:30 (9:30 PM)
        'duration': 75
    },
    {
        'name': 'William',
        'location': 'Union Square',
        'start': 645,       # 10:45 AM
        'end': 1050,       # 17:30 (5:30 PM)
        'duration': 45
    },
    {
        'name': 'Elizabeth',
        'location': 'Nob Hill',
        'start': 735,       # 12:15 PM
        'end': 900,        # 15:00 (3:00 PM)
        'duration': 105
    },
    {
        'name': 'Joseph',
        'location': 'Fisherman\'s Wharf',
        'start': 765,       # 12:45 PM
        'end': 840,        # 14:00 (2:00 PM)
        'duration': 75
    },
    {
        'name': 'Anthony',
        'location': 'Golden Gate Park',
        'start': 780,       # 13:00 (1:00 PM)
        'end': 1260,       # 21:00 (8:00 PM)
        'duration': 75
    },
    {
        'name': 'Barbara',
        'location': 'Embarcadero',
        'start': 1155,      # 19:15 (7:15 PM)
        'end': 1260,       # 21:00 (9:00 PM)
        'duration': 75
    },
    {
        'name': 'Carol',
        'location': 'Financial District',
        'start': 705,       # 11:45 AM
        'end': 990,        # 16:30 (4:15 PM)
        'duration': 60
    },
    {
        'name': 'Sandra',
        'location': 'North Beach',
        'start': 600,       # 10:00 AM
        'end': 750,        # 12:30 PM
        'duration': 15
    },
    {
        'name': 'Kenneth',
        'location': 'Presidio',
        'start': 1335,      # 22:15 (9:15 PM)
        'end': 1380,       # 23:00 (10:00 PM)
        'duration': 45
    }
]

def minutes_to_time(m):
    hours = m // 60
    mins = m % 60
    return f"{hours}:{mins:02d}"

best_itinerary = []
max_meetings = 0

for perm in itertools.permutations(friends):
    current_time = 540  # 9:00 AM
    current_location = 'Marina District'
    itinerary = []
    
    for friend in perm:
        travel = travel_times.get((current_location, friend['location']), None)
        if travel is None:
            continue
        
        arrival = current_time + travel
        meeting_start = max(arrival, friend['start'])
        meeting_end = meeting_start + friend['duration']
        
        if meeting_end > friend['end']:
            continue
        
        itinerary.append({
            'action': 'meet',
            'location': friend['location'],
            'person': friend['name'],
            'start_time': minutes_to_time(meeting_start),
            'end_time': minutes_to_time(meeting_end)
        })
        
        current_time = meeting_end
        current_location = friend['location']
    
    if len(itinerary) > max_meetings:
        max_meetings = len(itinerary)
        best_itinerary = itinerary

output = {
    "itinerary": best_itinerary
}

print(json.dumps(output))