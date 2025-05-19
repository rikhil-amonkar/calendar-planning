import itertools
import json

def format_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

travel_times = {
    ('Golden Gate Park', 'Haight-Ashbury'): 7,
    ('Golden Gate Park', 'Fisherman\'s Wharf'): 24,
    ('Golden Gate Park', 'The Castro'): 13,
    ('Golden Gate Park', 'Chinatown'): 23,
    ('Golden Gate Park', 'Alamo Square'): 10,
    ('Golden Gate Park', 'North Beach'): 24,
    ('Golden Gate Park', 'Russian Hill'): 19,
    ('Haight-Ashbury', 'Golden Gate Park'): 7,
    ('Haight-Ashbury', 'Fisherman\'s Wharf'): 23,
    ('Haight-Ashbury', 'The Castro'): 6,
    ('Haight-Ashbury', 'Chinatown'): 19,
    ('Haight-Ashbury', 'Alamo Square'): 5,
    ('Haight-Ashbury', 'North Beach'): 19,
    ('Haight-Ashbury', 'Russian Hill'): 17,
    ('Fisherman\'s Wharf', 'Golden Gate Park'): 25,
    ('Fisherman\'s Wharf', 'Haight-Ashbury'): 22,
    ('Fisherman\'s Wharf', 'The Castro'): 26,
    ('Fisherman\'s Wharf', 'Chinatown'): 12,
    ('Fisherman\'s Wharf', 'Alamo Square'): 20,
    ('Fisherman\'s Wharf', 'North Beach'): 6,
    ('Fisherman\'s Wharf', 'Russian Hill'): 7,
    ('The Castro', 'Golden Gate Park'): 11,
    ('The Castro', 'Haight-Ashbury'): 6,
    ('The Castro', 'Fisherman\'s Wharf'): 24,
    ('The Castro', 'Chinatown'): 20,
    ('The Castro', 'Alamo Square'): 8,
    ('The Castro', 'North Beach'): 20,
    ('The Castro', 'Russian Hill'): 18,
    ('Chinatown', 'Golden Gate Park'): 23,
    ('Chinatown', 'Haight-Ashbury'): 19,
    ('Chinatown', 'Fisherman\'s Wharf'): 8,
    ('Chinatown', 'The Castro'): 22,
    ('Chinatown', 'Alamo Square'): 17,
    ('Chinatown', 'North Beach'): 3,
    ('Chinatown', 'Russian Hill'): 7,
    ('Alamo Square', 'Golden Gate Park'): 9,
    ('Alamo Square', 'Haight-Ashbury'): 5,
    ('Alamo Square', 'Fisherman\'s Wharf'): 19,
    ('Alamo Square', 'The Castro'): 8,
    ('Alamo Square', 'Chinatown'): 16,
    ('Alamo Square', 'North Beach'): 15,
    ('Alamo Square', 'Russian Hill'): 13,
    ('North Beach', 'Golden Gate Park'): 22,
    ('North Beach', 'Haight-Ashbury'): 18,
    ('North Beach', 'Fisherman\'s Wharf'): 5,
    ('North Beach', 'The Castro'): 22,
    ('North Beach', 'Chinatown'): 6,
    ('North Beach', 'Alamo Square'): 16,
    ('North Beach', 'Russian Hill'): 4,
    ('Russian Hill', 'Golden Gate Park'): 21,
    ('Russian Hill', 'Haight-Ashbury'): 17,
    ('Russian Hill', 'Fisherman\'s Wharf'): 7,
    ('Russian Hill', 'The Castro'): 21,
    ('Russian Hill', 'Chinatown'): 9,
    ('Russian Hill', 'Alamo Square'): 15,
    ('Russian Hill', 'North Beach'): 5,
}

friends = [
    {
        'location': 'Haight-Ashbury',
        'name': 'Carol',
        'start': 1710,  # 9:30 PM
        'end': 1800,    # 10:30 PM
        'duration': 60
    },
    {
        'location': 'Fisherman\'s Wharf',
        'name': 'Laura',
        'start': 705,    # 11:45 AM
        'end': 1710,    # 9:30 PM
        'duration': 60
    },
    {
        'location': 'The Castro',
        'name': 'Karen',
        'start': 435,    # 7:15 AM
        'end': 840,     # 2:00 PM
        'duration': 75
    },
    {
        'location': 'Chinatown',
        'name': 'Elizabeth',
        'start': 735,    # 12:15 PM
        'end': 1710,    # 9:30 PM
        'duration': 75
    },
    {
        'location': 'Alamo Square',
        'name': 'Deborah',
        'start': 720,    # 12:00 PM
        'end': 900,     # 3:00 PM
        'duration': 105
    },
    {
        'location': 'North Beach',
        'name': 'Jason',
        'start': 1025,   # 2:45 PM
        'end': 1260,    # 7:00 PM
        'duration': 90
    },
    {
        'location': 'Russian Hill',
        'name': 'Steven',
        'start': 1025,   # 2:45 PM
        'end': 1170,    # 6:30 PM
        'duration': 120
    }
]

for perm in itertools.permutations(friends):
    current_time = 540  # 9:00 AM
    current_location = 'Golden Gate Park'
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
        current_location = 'Golden Gate Park'
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
            if max_meetings == 6:
                print(json.dumps({'itinerary': best_itinerary}))
                exit()

print(json.dumps({'itinerary': best_itinerary}))