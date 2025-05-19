import itertools
import json

travel_times = {
    ('Union Square', 'The Castro'): 17,
    ('Union Square', 'North Beach'): 10,
    ('Union Square', 'Embarcadero'): 11,
    ('Union Square', 'Alamo Square'): 15,
    ('Union Square', 'Nob Hill'): 9,
    ('Union Square', 'Presidio'): 24,
    ('Union Square', 'Fisherman\'s Wharf'): 15,
    ('Union Square', 'Mission District'): 14,
    ('Union Square', 'Haight-Ashbury'): 18,
    ('The Castro', 'Union Square'): 19,
    ('The Castro', 'North Beach'): 20,
    ('The Castro', 'Embarcadero'): 22,
    ('The Castro', 'Alamo Square'): 8,
    ('The Castro', 'Nob Hill'): 16,
    ('The Castro', 'Presidio'): 20,
    ('The Castro', 'Fisherman\'s Wharf'): 24,
    ('The Castro', 'Mission District'): 7,
    ('The Castro', 'Haight-Ashbury'): 6,
    ('North Beach', 'Union Square'): 7,
    ('North Beach', 'The Castro'): 23,
    ('North Beach', 'Embarcadero'): 6,
    ('North Beach', 'Alamo Square'): 16,
    ('North Beach', 'Nob Hill'): 7,
    ('North Beach', 'Presidio'): 17,
    ('North Beach', 'Fisherman\'s Wharf'): 5,
    ('North Beach', 'Mission District'): 18,
    ('North Beach', 'Haight-Ashbury'): 18,
    ('Embarcadero', 'Union Square'): 10,
    ('Embarcadero', 'The Castro'): 25,
    ('Embarcadero', 'North Beach'): 5,
    ('Embarcadero', 'Alamo Square'): 19,
    ('Embarcadero', 'Nob Hill'): 10,
    ('Embarcadero', 'Presidio'): 20,
    ('Embarcadero', 'Fisherman\'s Wharf'): 6,
    ('Embarcadero', 'Mission District'): 20,
    ('Embarcadero', 'Haight-Ashbury'): 21,
    ('Alamo Square', 'Union Square'): 14,
    ('Alamo Square', 'The Castro'): 8,
    ('Alamo Square', 'North Beach'): 15,
    ('Alamo Square', 'Embarcadero'): 16,
    ('Alamo Square', 'Nob Hill'): 11,
    ('Alamo Square', 'Presidio'): 17,
    ('Alamo Square', 'Fisherman\'s Wharf'): 19,
    ('Alamo Square', 'Mission District'): 10,
    ('Alamo Square', 'Haight-Ashbury'): 5,
    ('Nob Hill', 'Union Square'): 7,
    ('Nob Hill', 'The Castro'): 17,
    ('Nob Hill', 'North Beach'): 8,
    ('Nob Hill', 'Embarcadero'): 9,
    ('Nob Hill', 'Alamo Square'): 11,
    ('Nob Hill', 'Presidio'): 17,
    ('Nob Hill', 'Fisherman\'s Wharf'): 10,
    ('Nob Hill', 'Mission District'): 13,
    ('Nob Hill', 'Haight-Ashbury'): 13,
    ('Presidio', 'Union Square'): 22,
    ('Presidio', 'The Castro'): 21,
    ('Presidio', 'North Beach'): 18,
    ('Presidio', 'Embarcadero'): 20,
    ('Presidio', 'Alamo Square'): 19,
    ('Presidio', 'Nob Hill'): 18,
    ('Presidio', 'Fisherman\'s Wharf'): 19,
    ('Presidio', 'Mission District'): 26,
    ('Presidio', 'Haight-Ashbury'): 15,
    ('Fisherman\'s Wharf', 'Union Square'): 13,
    ('Fisherman\'s Wharf', 'The Castro'): 27,
    ('Fisherman\'s Wharf', 'North Beach'): 6,
    ('Fisherman\'s Wharf', 'Embarcadero'): 8,
    ('Fisherman\'s Wharf', 'Alamo Square'): 21,
    ('Fisherman\'s Wharf', 'Nob Hill'): 11,
    ('Fisherman\'s Wharf', 'Presidio'): 17,
    ('Fisherman\'s Wharf', 'Mission District'): 22,
    ('Fisherman\'s Wharf', 'Haight-Ashbury'): 22,
    ('Mission District', 'Union Square'): 15,
    ('Mission District', 'The Castro'): 7,
    ('Mission District', 'North Beach'): 17,
    ('Mission District', 'Embarcadero'): 19,
    ('Mission District', 'Alamo Square'): 11,
    ('Mission District', 'Nob Hill'): 12,
    ('Mission District', 'Presidio'): 25,
    ('Mission District', 'Fisherman\'s Wharf'): 22,
    ('Mission District', 'Haight-Ashbury'): 12,
    ('Haight-Ashbury', 'Union Square'): 19,
    ('Haight-Ashbury', 'The Castro'): 6,
    ('Haight-Ashbury', 'North Beach'): 19,
    ('Haight-Ashbury', 'Embarcadero'): 20,
    ('Haight-Ashbury', 'Alamo Square'): 5,
    ('Haight-Ashbury', 'Nob Hill'): 15,
    ('Haight-Ashbury', 'Presidio'): 15,
    ('Haight-Ashbury', 'Fisherman\'s Wharf'): 23,
    ('Haight-Ashbury', 'Mission District'): 11,
}

friends = [
    {
        'name': 'Melissa',
        'location': 'The Castro',
        'start': 1020 - 45,  # 16:15 (4:15 PM) converted to minutes since midnight
        'end': 1410,        # 23:30 (9:30 PM)
        'duration': 30
    },
    {
        'name': 'Kimberly',
        'location': 'North Beach',
        'start': 420,       # 7:00 AM
        'end': 630,        # 10:30 AM
        'duration': 15
    },
    {
        'name': 'Joseph',
        'location': 'Embarcadero',
        'start': 810,       # 13:30 (1:30 PM)
        'end': 1410,       # 23:30 (9:30 PM)
        'duration': 75
    },
    {
        'name': 'Barbara',
        'location': 'Alamo Square',
        'start': 1335,      # 22:15 (9:15 PM)
        'end': 1410,       # 23:45 (9:45 PM)
        'duration': 15
    },
    {
        'name': 'Kenneth',
        'location': 'Nob Hill',
        'start': 735,       # 12:15 PM
        'end': 990,        # 16:30 (4:30 PM)
        'duration': 105
    },
    {
        'name': 'Joshua',
        'location': 'Presidio',
        'start': 1020,      # 17:00 (5:00 PM)
        'end': 1170,       # 19:15 (6:15 PM)
        'duration': 105
    },
    {
        'name': 'Brian',
        'location': 'Fisherman\'s Wharf',
        'start': 570,       # 9:30 AM
        'end': 990,        # 16:30 (4:30 PM)
        'duration': 45
    },
    {
        'name': 'Steven',
        'location': 'Mission District',
        'start': 1125,      # 18:45 (6:45 PM)
        'end': 1260,       # 21:00 (9:00 PM)
        'duration': 90
    },
    {
        'name': 'Betty',
        'location': 'Haight-Ashbury',
        'start': 1050,      # 17:30 (5:30 PM)
        'end': 1260,       # 21:00 (9:00 PM)
        'duration': 90
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