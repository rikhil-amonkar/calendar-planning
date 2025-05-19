import itertools
import json

travel_times = {
    ('Union Square', 'Mission District'): 14,
    ('Union Square', 'Fisherman\'s Wharf'): 15,
    ('Union Square', 'Russian Hill'): 13,
    ('Union Square', 'Marina District'): 18,
    ('Union Square', 'North Beach'): 10,
    ('Union Square', 'Chinatown'): 7,
    ('Union Square', 'Pacific Heights'): 15,
    ('Union Square', 'The Castro'): 17,
    ('Union Square', 'Nob Hill'): 9,
    ('Union Square', 'Sunset District'): 27,
    ('Mission District', 'Union Square'): 15,
    ('Mission District', 'Fisherman\'s Wharf'): 22,
    ('Mission District', 'Russian Hill'): 15,
    ('Mission District', 'Marina District'): 19,
    ('Mission District', 'North Beach'): 17,
    ('Mission District', 'Chinatown'): 16,
    ('Mission District', 'Pacific Heights'): 16,
    ('Mission District', 'The Castro'): 7,
    ('Mission District', 'Nob Hill'): 12,
    ('Mission District', 'Sunset District'): 24,
    ('Fisherman\'s Wharf', 'Union Square'): 13,
    ('Fisherman\'s Wharf', 'Mission District'): 22,
    ('Fisherman\'s Wharf', 'Russian Hill'): 7,
    ('Fisherman\'s Wharf', 'Marina District'): 9,
    ('Fisherman\'s Wharf', 'North Beach'): 6,
    ('Fisherman\'s Wharf', 'Chinatown'): 12,
    ('Fisherman\'s Wharf', 'Pacific Heights'): 12,
    ('Fisherman\'s Wharf', 'The Castro'): 27,
    ('Fisherman\'s Wharf', 'Nob Hill'): 11,
    ('Fisherman\'s Wharf', 'Sunset District'): 27,
    ('Russian Hill', 'Union Square'): 10,
    ('Russian Hill', 'Mission District'): 16,
    ('Russian Hill', 'Fisherman\'s Wharf'): 7,
    ('Russian Hill', 'Marina District'): 7,
    ('Russian Hill', 'North Beach'): 5,
    ('Russian Hill', 'Chinatown'): 9,
    ('Russian Hill', 'Pacific Heights'): 7,
    ('Russian Hill', 'The Castro'): 21,
    ('Russian Hill', 'Nob Hill'): 5,
    ('Russian Hill', 'Sunset District'): 23,
    ('Marina District', 'Union Square'): 16,
    ('Marina District', 'Mission District'): 20,
    ('Marina District', 'Fisherman\'s Wharf'): 10,
    ('Marina District', 'Russian Hill'): 8,
    ('Marina District', 'North Beach'): 11,
    ('Marina District', 'Chinatown'): 15,
    ('Marina District', 'Pacific Heights'): 7,
    ('Marina District', 'The Castro'): 22,
    ('Marina District', 'Nob Hill'): 12,
    ('Marina District', 'Sunset District'): 19,
    ('North Beach', 'Union Square'): 7,
    ('North Beach', 'Mission District'): 18,
    ('North Beach', 'Fisherman\'s Wharf'): 5,
    ('North Beach', 'Russian Hill'): 4,
    ('North Beach', 'Marina District'): 9,
    ('North Beach', 'Chinatown'): 6,
    ('North Beach', 'Pacific Heights'): 8,
    ('North Beach', 'The Castro'): 23,
    ('North Beach', 'Nob Hill'): 7,
    ('North Beach', 'Sunset District'): 27,
    ('Chinatown', 'Union Square'): 7,
    ('Chinatown', 'Mission District'): 17,
    ('Chinatown', 'Fisherman\'s Wharf'): 8,
    ('Chinatown', 'Russian Hill'): 7,
    ('Chinatown', 'Marina District'): 12,
    ('Chinatown', 'North Beach'): 3,
    ('Chinatown', 'Pacific Heights'): 10,
    ('Chinatown', 'The Castro'): 22,
    ('Chinatown', 'Nob Hill'): 9,
    ('Chinatown', 'Sunset District'): 29,
    ('Pacific Heights', 'Union Square'): 12,
    ('Pacific Heights', 'Mission District'): 15,
    ('Pacific Heights', 'Fisherman\'s Wharf'): 13,
    ('Pacific Heights', 'Russian Hill'): 7,
    ('Pacific Heights', 'Marina District'): 6,
    ('Pacific Heights', 'North Beach'): 9,
    ('Pacific Heights', 'Chinatown'): 11,
    ('Pacific Heights', 'The Castro'): 16,
    ('Pacific Heights', 'Nob Hill'): 8,
    ('Pacific Heights', 'Sunset District'): 21,
    ('The Castro', 'Union Square'): 19,
    ('The Castro', 'Mission District'): 7,
    ('The Castro', 'Fisherman\'s Wharf'): 24,
    ('The Castro', 'Russian Hill'): 18,
    ('The Castro', 'Marina District'): 21,
    ('The Castro', 'North Beach'): 20,
    ('The Castro', 'Chinatown'): 22,
    ('The Castro', 'Pacific Heights'): 16,
    ('The Castro', 'Nob Hill'): 16,
    ('The Castro', 'Sunset District'): 17,
    ('Nob Hill', 'Union Square'): 7,
    ('Nob Hill', 'Mission District'): 13,
    ('Nob Hill', 'Fisherman\'s Wharf'): 10,
    ('Nob Hill', 'Russian Hill'): 5,
    ('Nob Hill', 'Marina District'): 11,
    ('Nob Hill', 'North Beach'): 8,
    ('Nob Hill', 'Chinatown'): 6,
    ('Nob Hill', 'Pacific Heights'): 8,
    ('Nob Hill', 'The Castro'): 17,
    ('Nob Hill', 'Sunset District'): 24,
    ('Sunset District', 'Union Square'): 30,
    ('Sunset District', 'Mission District'): 25,
    ('Sunset District', 'Fisherman\'s Wharf'): 29,
    ('Sunset District', 'Russian Hill'): 24,
    ('Sunset District', 'Marina District'): 21,
    ('Sunset District', 'North Beach'): 28,
    ('Sunset District', 'Chinatown'): 30,
    ('Sunset District', 'Pacific Heights'): 21,
    ('Sunset District', 'The Castro'): 17,
    ('Sunset District', 'Nob Hill'): 27,
}

friends = [
    {
        'name': 'Kevin',
        'location': 'Mission District',
        'start': 1260,  # 21:00 (9:00 PM)
        'end': 1365,   # 22:45 (10:45 PM)
        'duration': 60
    },
    {
        'name': 'Mark',
        'location': 'Fisherman\'s Wharf',
        'start': 1170,  # 19:30 (5:30 PM)
        'end': 1320,   # 22:00 (10:00 PM)
        'duration': 90
    },
    {
        'name': 'Jessica',
        'location': 'Russian Hill',
        'start': 540,   # 9:00 AM
        'end': 900,    # 15:00 (3:00 PM)
        'duration': 120
    },
    {
        'name': 'Jason',
        'location': 'Marina District',
        'start': 945,   # 15:45 (3:45 PM)
        'end': 1410,   # 23:50 (11:50 PM)
        'duration': 120
    },
    {
        'name': 'John',
        'location': 'North Beach',
        'start': 585,   # 9:45 AM
        'end': 1080,   # 18:00 (6:00 PM)
        'duration': 15
    },
    {
        'name': 'Karen',
        'location': 'Chinatown',
        'start': 1125,  # 18:45 (6:45 PM)
        'end': 1260,   # 21:00 (9:00 PM)
        'duration': 75
    },
    {
        'name': 'Sarah',
        'location': 'Pacific Heights',
        'start': 1050,  # 17:30 (5:30 PM)
        'end': 1115,   # 18:15 (6:15 PM)
        'duration': 45
    },
    {
        'name': 'Amanda',
        'location': 'The Castro',
        'start': 1200,  # 20:00 (8:00 PM)
        'end': 1290,   # 21:30 (9:30 PM)
        'duration': 60
    },
    {
        'name': 'Nancy',
        'location': 'Nob Hill',
        'start': 585,   # 9:45 AM
        'end': 810,    # 13:30 (1:30 PM)
        'duration': 45
    },
    {
        'name': 'Rebecca',
        'location': 'Sunset District',
        'start': 570,   # 9:30 AM
        'end': 900,    # 15:00 (3:00 PM)
        'duration': 75
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
    current_location = 'Union Square'
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