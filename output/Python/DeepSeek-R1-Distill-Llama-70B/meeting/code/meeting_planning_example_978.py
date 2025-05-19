import itertools
import json

def format_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

travel_times = {
    ('Embarcadero', 'Fisherman\'s Wharf'): 6,
    ('Embarcadero', 'Financial District'): 5,
    ('Embarcadero', 'Russian Hill'): 8,
    ('Embarcadero', 'Marina District'): 12,
    ('Embarcadero', 'Richmond District'): 21,
    ('Embarcadero', 'Pacific Heights'): 11,
    ('Embarcadero', 'Haight-Ashbury'): 21,
    ('Embarcadero', 'Presidio'): 20,
    ('Embarcadero', 'Nob Hill'): 10,
    ('Embarcadero', 'The Castro'): 25,
    ('Fisherman\'s Wharf', 'Embarcadero'): 8,
    ('Fisherman\'s Wharf', 'Financial District'): 11,
    ('Fisherman\'s Wharf', 'Russian Hill'): 7,
    ('Fisherman\'s Wharf', 'Marina District'): 9,
    ('Fisherman\'s Wharf', 'Richmond District'): 18,
    ('Fisherman\'s Wharf', 'Pacific Heights'): 12,
    ('Fisherman\'s Wharf', 'Haight-Ashbury'): 22,
    ('Fisherman\'s Wharf', 'Presidio'): 17,
    ('Fisherman\'s Wharf', 'Nob Hill'): 11,
    ('Fisherman\'s Wharf', 'The Castro'): 27,
    ('Financial District', 'Embarcadero'): 4,
    ('Financial District', 'Fisherman\'s Wharf'): 10,
    ('Financial District', 'Russian Hill'): 11,
    ('Financial District', 'Marina District'): 15,
    ('Financial District', 'Richmond District'): 21,
    ('Financial District', 'Pacific Heights'): 13,
    ('Financial District', 'Haight-Ashbury'): 19,
    ('Financial District', 'Presidio'): 22,
    ('Financial District', 'Nob Hill'): 8,
    ('Financial District', 'The Castro'): 20,
    ('Russian Hill', 'Embarcadero'): 8,
    ('Russian Hill', 'Fisherman\'s Wharf'): 7,
    ('Russian Hill', 'Financial District'): 11,
    ('Russian Hill', 'Marina District'): 7,
    ('Russian Hill', 'Richmond District'): 14,
    ('Russian Hill', 'Pacific Heights'): 7,
    ('Russian Hill', 'Haight-Ashbury'): 17,
    ('Russian Hill', 'Presidio'): 14,
    ('Russian Hill', 'Nob Hill'): 5,
    ('Russian Hill', 'The Castro'): 21,
    ('Marina District', 'Embarcadero'): 14,
    ('Marina District', 'Fisherman\'s Wharf'): 10,
    ('Marina District', 'Financial District'): 17,
    ('Marina District', 'Russian Hill'): 8,
    ('Marina District', 'Richmond District'): 11,
    ('Marina District', 'Pacific Heights'): 7,
    ('Marina District', 'Haight-Ashbury'): 16,
    ('Marina District', 'Presidio'): 10,
    ('Marina District', 'Nob Hill'): 12,
    ('Marina District', 'The Castro'): 22,
    ('Richmond District', 'Embarcadero'): 19,
    ('Richmond District', 'Fisherman\'s Wharf'): 18,
    ('Richmond District', 'Financial District'): 22,
    ('Richmond District', 'Russian Hill'): 13,
    ('Richmond District', 'Marina District'): 9,
    ('Richmond District', 'Pacific Heights'): 10,
    ('Richmond District', 'Haight-Ashbury'): 10,
    ('Richmond District', 'Presidio'): 7,
    ('Richmond District', 'Nob Hill'): 17,
    ('Richmond District', 'The Castro'): 16,
    ('Pacific Heights', 'Embarcadero'): 10,
    ('Pacific Heights', 'Fisherman\'s Wharf'): 13,
    ('Pacific Heights', 'Financial District'): 13,
    ('Pacific Heights', 'Russian Hill'): 7,
    ('Pacific Heights', 'Marina District'): 6,
    ('Pacific Heights', 'Richmond District'): 12,
    ('Pacific Heights', 'Haight-Ashbury'): 11,
    ('Pacific Heights', 'Presidio'): 11,
    ('Pacific Heights', 'Nob Hill'): 8,
    ('Pacific Heights', 'The Castro'): 16,
    ('Haight-Ashbury', 'Embarcadero'): 20,
    ('Haight-Ashbury', 'Fisherman\'s Wharf'): 23,
    ('Haight-Ashbury', 'Financial District'): 21,
    ('Haight-Ashbury', 'Russian Hill'): 17,
    ('Haight-Ashbury', 'Marina District'): 17,
    ('Haight-Ashbury', 'Richmond District'): 10,
    ('Haight-Ashbury', 'Pacific Heights'): 12,
    ('Haight-Ashbury', 'Presidio'): 15,
    ('Haight-Ashbury', 'Nob Hill'): 15,
    ('Haight-Ashbury', 'The Castro'): 6,
    ('Presidio', 'Embarcadero'): 20,
    ('Presidio', 'Fisherman\'s Wharf'): 19,
    ('Presidio', 'Financial District'): 23,
    ('Presidio', 'Russian Hill'): 14,
    ('Presidio', 'Marina District'): 11,
    ('Presidio', 'Richmond District'): 7,
    ('Presidio', 'Pacific Heights'): 11,
    ('Presidio', 'Haight-Ashbury'): 15,
    ('Presidio', 'Nob Hill'): 18,
    ('Presidio', 'The Castro'): 21,
    ('Nob Hill', 'Embarcadero'): 9,
    ('Nob Hill', 'Fisherman\'s Wharf'): 10,
    ('Nob Hill', 'Financial District'): 9,
    ('Nob Hill', 'Russian Hill'): 5,
    ('Nob Hill', 'Marina District'): 11,
    ('Nob Hill', 'Richmond District'): 14,
    ('Nob Hill', 'Pacific Heights'): 8,
    ('Nob Hill', 'Haight-Ashbury'): 13,
    ('Nob Hill', 'Presidio'): 17,
    ('Nob Hill', 'The Castro'): 17,
    ('The Castro', 'Embarcadero'): 22,
    ('The Castro', 'Fisherman\'s Wharf'): 24,
    ('The Castro', 'Financial District'): 21,
    ('The Castro', 'Russian Hill'): 18,
    ('The Castro', 'Marina District'): 21,
    ('The Castro', 'Richmond District'): 16,
    ('The Castro', 'Pacific Heights'): 16,
    ('The Castro', 'Haight-Ashbury'): 6,
    ('The Castro', 'Presidio'): 20,
    ('The Castro', 'Nob Hill'): 16,
}

friends = [
    {
        'location': 'Fisherman\'s Wharf',
        'name': 'Stephanie',
        'start': 1050,  # 3:30 PM
        'end': 1800,    # 10:00 PM
        'duration': 30
    },
    {
        'location': 'Financial District',
        'name': 'Lisa',
        'start': 645,    # 10:45 AM
        'end': 1155,    # 5:15 PM
        'duration': 15
    },
    {
        'location': 'Russian Hill',
        'name': 'Melissa',
        'start': 1140,  # 5:00 PM
        'end': 1785,    # 9:45 PM
        'duration': 120
    },
    {
        'location': 'Marina District',
        'name': 'Betty',
        'start': 645,    # 10:45 AM
        'end': 855,     # 2:15 PM
        'duration': 60
    },
    {
        'location': 'Richmond District',
        'name': 'Sarah',
        'start': 975,    # 4:15 PM
        'end': 1350,    # 7:30 PM
        'duration': 105
    },
    {
        'location': 'Pacific Heights',
        'name': 'Daniel',
        'start': 1170,  # 6:30 PM
        'end': 1785,    # 9:45 PM
        'duration': 60
    },
    {
        'location': 'Haight-Ashbury',
        'name': 'Joshua',
        'start': 540,    # 9:00 AM
        'end': 990,     # 3:30 PM
        'duration': 15
    },
    {
        'location': 'Presidio',
        'name': 'Joseph',
        'start': 420,    # 7:00 AM
        'end': 780,     # 1:00 PM
        'duration': 45
    },
    {
        'location': 'Nob Hill',
        'name': 'Andrew',
        'start': 1425,   # 7:45 PM
        'end': 1800,    # 10:00 PM
        'duration': 105
    },
    {
        'location': 'The Castro',
        'name': 'John',
        'start': 765,    # 1:15 PM
        'end': 1425,    # 7:45 PM
        'duration': 45
    }
]

for perm in itertools.permutations(friends):
    current_time = 540  # 9:00 AM
    current_location = 'Embarcadero'
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

# If no permutation meets all friends, check for permutations with fewer friends
max_meetings = 0
best_itinerary = []
for r in range(len(friends)-1, 0, -1):
    for perm in itertools.permutations(friends, r):
        current_time = 540
        current_location = 'Embarcadero'
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
            if max_meetings == 9:
                print(json.dumps({'itinerary': best_itinerary}))
                exit()

print(json.dumps({'itinerary': best_itinerary}))