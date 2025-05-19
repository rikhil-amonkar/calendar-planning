import itertools

travel_times = {
    ('Russian Hill', 'Presidio'): 14,
    ('Russian Hill', 'Chinatown'): 9,
    ('Russian Hill', 'Pacific Heights'): 7,
    ('Russian Hill', 'Richmond District'): 14,
    ('Russian Hill', 'Fisherman\'s Wharf'): 7,
    ('Russian Hill', 'Golden Gate Park'): 21,
    ('Russian Hill', 'Bayview'): 23,
    ('Presidio', 'Russian Hill'): 14,
    ('Presidio', 'Chinatown'): 21,
    ('Presidio', 'Pacific Heights'): 11,
    ('Presidio', 'Richmond District'): 7,
    ('Presidio', 'Fisherman\'s Wharf'): 19,
    ('Presidio', 'Golden Gate Park'): 12,
    ('Presidio', 'Bayview'): 31,
    ('Chinatown', 'Russian Hill'): 7,
    ('Chinatown', 'Presidio'): 19,
    ('Chinatown', 'Pacific Heights'): 10,
    ('Chinatown', 'Richmond District'): 20,
    ('Chinatown', 'Fisherman\'s Wharf'): 8,
    ('Chinatown', 'Golden Gate Park'): 23,
    ('Chinatown', 'Bayview'): 22,
    ('Pacific Heights', 'Russian Hill'): 7,
    ('Pacific Heights', 'Presidio'): 11,
    ('Pacific Heights', 'Chinatown'): 11,
    ('Pacific Heights', 'Richmond District'): 12,
    ('Pacific Heights', 'Fisherman\'s Wharf'): 13,
    ('Pacific Heights', 'Golden Gate Park'): 15,
    ('Pacific Heights', 'Bayview'): 22,
    ('Richmond District', 'Russian Hill'): 13,
    ('Richmond District', 'Presidio'): 7,
    ('Richmond District', 'Chinatown'): 20,
    ('Richmond District', 'Pacific Heights'): 10,
    ('Richmond District', 'Fisherman\'s Wharf'): 18,
    ('Richmond District', 'Golden Gate Park'): 9,
    ('Richmond District', 'Bayview'): 26,
    ('Fisherman\'s Wharf', 'Russian Hill'): 7,
    ('Fisherman\'s Wharf', 'Presidio'): 17,
    ('Fisherman\'s Wharf', 'Chinatown'): 12,
    ('Fisherman\'s Wharf', 'Pacific Heights'): 12,
    ('Fisherman\'s Wharf', 'Richmond District'): 18,
    ('Fisherman\'s Wharf', 'Golden Gate Park'): 25,
    ('Fisherman\'s Wharf', 'Bayview'): 26,
    ('Golden Gate Park', 'Russian Hill'): 19,
    ('Golden Gate Park', 'Presidio'): 11,
    ('Golden Gate Park', 'Chinatown'): 23,
    ('Golden Gate Park', 'Pacific Heights'): 16,
    ('Golden Gate Park', 'Richmond District'): 7,
    ('Golden Gate Park', 'Fisherman\'s Wharf'): 24,
    ('Golden Gate Park', 'Bayview'): 23,
    ('Bayview', 'Russian Hill'): 23,
    ('Bayview', 'Presidio'): 31,
    ('Bayview', 'Chinatown'): 18,
    ('Bayview', 'Pacific Heights'): 23,
    ('Bayview', 'Richmond District'): 25,
    ('Bayview', 'Fisherman\'s Wharf'): 25,
    ('Bayview', 'Golden Gate Park'): 22,
}

friends = [
    {
        'name': 'Matthew',
        'location': 'Presidio',
        'start': 660,  # 11:00 AM
        'end': 1260,   # 21:00 (9:00 PM)
        'duration': 90
    },
    {
        'name': 'Margaret',
        'location': 'Chinatown',
        'start': 555,  # 9:15 AM
        'end': 1185,  # 19:45 (6:45 PM)
        'duration': 90
    },
    {
        'name': 'Nancy',
        'location': 'Pacific Heights',
        'start': 855,  # 14:15 (2:15 PM)
        'end': 1020,  # 17:00 (5:00 PM)
        'duration': 15
    },
    {
        'name': 'Helen',
        'location': 'Richmond District',
        'start': 1125, # 18:45 (6:45 PM)
        'end': 1200,  # 20:00 (8:00 PM)
        'duration': 60
    },
    {
        'name': 'Rebecca',
        'location': 'Fisherman\'s Wharf',
        'start': 1215, # 20:15 (8:15 PM)
        'end': 1260,  # 21:00 (9:00 PM)
        'duration': 60
    },
    {
        'name': 'Kimberly',
        'location': 'Golden Gate Park',
        'start': 780,  # 13:00 (1:00 PM)
        'end': 990,   # 16:30 (4:30 PM)
        'duration': 120
    },
    {
        'name': 'Kenneth',
        'location': 'Bayview',
        'start': 870,  # 14:30 (2:30 PM)
        'end': 1080,  # 18:00 (6:00 PM)
        'duration': 60
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
    current_location = 'Russian Hill'
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

import json
print(json.dumps(output))