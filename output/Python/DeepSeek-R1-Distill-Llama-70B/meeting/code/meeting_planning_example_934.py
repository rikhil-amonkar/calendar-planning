import itertools
import json

def format_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

travel_times = {
    ('Nob Hill', 'Embarcadero'): 9,
    ('Nob Hill', 'The Castro'): 17,
    ('Nob Hill', 'Haight-Ashbury'): 13,
    ('Nob Hill', 'Union Square'): 7,
    ('Nob Hill', 'North Beach'): 8,
    ('Nob Hill', 'Pacific Heights'): 8,
    ('Nob Hill', 'Chinatown'): 6,
    ('Nob Hill', 'Golden Gate Park'): 17,
    ('Nob Hill', 'Marina District'): 11,
    ('Nob Hill', 'Russian Hill'): 5,
    ('Embarcadero', 'Nob Hill'): 10,
    ('Embarcadero', 'The Castro'): 25,
    ('Embarcadero', 'Haight-Ashbury'): 21,
    ('Embarcadero', 'Union Square'): 10,
    ('Embarcadero', 'North Beach'): 5,
    ('Embarcadero', 'Pacific Heights'): 11,
    ('Embarcadero', 'Chinatown'): 7,
    ('Embarcadero', 'Golden Gate Park'): 25,
    ('Embarcadero', 'Marina District'): 12,
    ('Embarcadero', 'Russian Hill'): 8,
    ('The Castro', 'Nob Hill'): 16,
    ('The Castro', 'Embarcadero'): 22,
    ('The Castro', 'Haight-Ashbury'): 6,
    ('The Castro', 'Union Square'): 19,
    ('The Castro', 'North Beach'): 20,
    ('The Castro', 'Pacific Heights'): 16,
    ('The Castro', 'Chinatown'): 22,
    ('The Castro', 'Golden Gate Park'): 11,
    ('The Castro', 'Marina District'): 21,
    ('The Castro', 'Russian Hill'): 18,
    ('Haight-Ashbury', 'Nob Hill'): 15,
    ('Haight-Ashbury', 'Embarcadero'): 20,
    ('Haight-Ashbury', 'The Castro'): 6,
    ('Haight-Ashbury', 'Union Square'): 19,
    ('Haight-Ashbury', 'North Beach'): 19,
    ('Haight-Ashbury', 'Pacific Heights'): 12,
    ('Haight-Ashbury', 'Chinatown'): 19,
    ('Haight-Ashbury', 'Golden Gate Park'): 7,
    ('Haight-Ashbury', 'Marina District'): 17,
    ('Haight-Ashbury', 'Russian Hill'): 17,
    ('Union Square', 'Nob Hill'): 9,
    ('Union Square', 'Embarcadero'): 11,
    ('Union Square', 'The Castro'): 17,
    ('Union Square', 'Haight-Ashbury'): 18,
    ('Union Square', 'North Beach'): 10,
    ('Union Square', 'Pacific Heights'): 15,
    ('Union Square', 'Chinatown'): 7,
    ('Union Square', 'Golden Gate Park'): 22,
    ('Union Square', 'Marina District'): 18,
    ('Union Square', 'Russian Hill'): 13,
    ('North Beach', 'Nob Hill'): 7,
    ('North Beach', 'Embarcadero'): 6,
    ('North Beach', 'The Castro'): 23,
    ('North Beach', 'Haight-Ashbury'): 18,
    ('North Beach', 'Union Square'): 7,
    ('North Beach', 'Pacific Heights'): 8,
    ('North Beach', 'Chinatown'): 6,
    ('North Beach', 'Golden Gate Park'): 22,
    ('North Beach', 'Marina District'): 9,
    ('North Beach', 'Russian Hill'): 4,
    ('Pacific Heights', 'Nob Hill'): 8,
    ('Pacific Heights', 'Embarcadero'): 10,
    ('Pacific Heights', 'The Castro'): 16,
    ('Pacific Heights', 'Haight-Ashbury'): 11,
    ('Pacific Heights', 'Union Square'): 12,
    ('Pacific Heights', 'North Beach'): 9,
    ('Pacific Heights', 'Chinatown'): 11,
    ('Pacific Heights', 'Golden Gate Park'): 15,
    ('Pacific Heights', 'Marina District'): 6,
    ('Pacific Heights', 'Russian Hill'): 7,
    ('Chinatown', 'Nob Hill'): 9,
    ('Chinatown', 'Embarcadero'): 5,
    ('Chinatown', 'The Castro'): 22,
    ('Chinatown', 'Haight-Ashbury'): 19,
    ('Chinatown', 'Union Square'): 7,
    ('Chinatown', 'North Beach'): 3,
    ('Chinatown', 'Pacific Heights'): 10,
    ('Chinatown', 'Golden Gate Park'): 23,
    ('Chinatown', 'Marina District'): 12,
    ('Chinatown', 'Russian Hill'): 7,
    ('Golden Gate Park', 'Nob Hill'): 20,
    ('Golden Gate Park', 'Embarcadero'): 25,
    ('Golden Gate Park', 'The Castro'): 13,
    ('Golden Gate Park', 'Haight-Ashbury'): 7,
    ('Golden Gate Park', 'Union Square'): 22,
    ('Golden Gate Park', 'North Beach'): 23,
    ('Golden Gate Park', 'Pacific Heights'): 16,
    ('Golden Gate Park', 'Chinatown'): 23,
    ('Golden Gate Park', 'Marina District'): 16,
    ('Golden Gate Park', 'Russian Hill'): 19,
    ('Marina District', 'Nob Hill'): 12,
    ('Marina District', 'Embarcadero'): 14,
    ('Marina District', 'The Castro'): 22,
    ('Marina District', 'Haight-Ashbury'): 16,
    ('Marina District', 'Union Square'): 16,
    ('Marina District', 'North Beach'): 11,
    ('Marina District', 'Pacific Heights'): 7,
    ('Marina District', 'Chinatown'): 15,
    ('Marina District', 'Golden Gate Park'): 18,
    ('Marina District', 'Russian Hill'): 8,
    ('Russian Hill', 'Nob Hill'): 5,
    ('Russian Hill', 'Embarcadero'): 8,
    ('Russian Hill', 'The Castro'): 21,
    ('Russian Hill', 'Haight-Ashbury'): 17,
    ('Russian Hill', 'Union Square'): 10,
    ('Russian Hill', 'North Beach'): 5,
    ('Russian Hill', 'Pacific Heights'): 7,
    ('Russian Hill', 'Chinatown'): 9,
    ('Russian Hill', 'Golden Gate Park'): 21,
    ('Russian Hill', 'Marina District'): 7,
}

friends = [
    {
        'location': 'Embarcadero',
        'name': 'Mary',
        'start': 1680,  # 8:00 PM
        'end': 1775,    # 9:15 PM
        'duration': 75
    },
    {
        'location': 'The Castro',
        'name': 'Kenneth',
        'start': 675,    # 11:15 AM
        'end': 1350,    # 7:15 PM
        'duration': 30
    },
    {
        'location': 'Haight-Ashbury',
        'name': 'Joseph',
        'start': 1680,  # 8:00 PM
        'end': 1800,    # 10:00 PM
        'duration': 120
    },
    {
        'location': 'Union Square',
        'name': 'Sarah',
        'start': 705,    # 11:45 AM
        'end': 930,     # 2:30 PM
        'duration': 90
    },
    {
        'location': 'North Beach',
        'name': 'Thomas',
        'start': 1395,  # 7:15 PM
        'end': 1415,    # 7:45 PM
        'duration': 15
    },
    {
        'location': 'Pacific Heights',
        'name': 'Daniel',
        'start': 765,    # 1:45 PM
        'end': 1560,    # 8:30 PM
        'duration': 15
    },
    {
        'location': 'Chinatown',
        'name': 'Richard',
        'start': 480,    # 8:00 AM
        'end': 1265,    # 6:45 PM
        'duration': 30
    },
    {
        'location': 'Golden Gate Park',
        'name': 'Mark',
        'start': 1170,  # 5:30 PM
        'end': 1710,    # 9:30 PM
        'duration': 120
    },
    {
        'location': 'Marina District',
        'name': 'David',
        'start': 1680,  # 8:00 PM
        'end': 1740,    # 9:00 PM
        'duration': 60
    },
    {
        'location': 'Russian Hill',
        'name': 'Karen',
        'start': 735,    # 1:15 PM
        'end': 1170,    # 6:30 PM
        'duration': 120
    }
]

for perm in itertools.permutations(friends):
    current_time = 540  # 9:00 AM
    current_location = 'Nob Hill'
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
        current_location = 'Nob Hill'
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