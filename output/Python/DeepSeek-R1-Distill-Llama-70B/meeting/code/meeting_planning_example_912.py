import itertools
import json

travel_times = {
    ('Union Square', 'Presidio'): 24,
    ('Union Square', 'Alamo Square'): 15,
    ('Union Square', 'Marina District'): 18,
    ('Union Square', 'Financial District'): 9,
    ('Union Square', 'Nob Hill'): 9,
    ('Union Square', 'Sunset District'): 27,
    ('Union Square', 'Chinatown'): 7,
    ('Union Square', 'Russian Hill'): 13,
    ('Union Square', 'North Beach'): 10,
    ('Union Square', 'Haight-Ashbury'): 18,
    ('Presidio', 'Union Square'): 22,
    ('Presidio', 'Alamo Square'): 19,
    ('Presidio', 'Marina District'): 11,
    ('Presidio', 'Financial District'): 23,
    ('Presidio', 'Nob Hill'): 18,
    ('Presidio', 'Sunset District'): 15,
    ('Presidio', 'Chinatown'): 21,
    ('Presidio', 'Russian Hill'): 14,
    ('Presidio', 'North Beach'): 18,
    ('Presidio', 'Haight-Ashbury'): 15,
    ('Alamo Square', 'Union Square'): 14,
    ('Alamo Square', 'Presidio'): 17,
    ('Alamo Square', 'Marina District'): 15,
    ('Alamo Square', 'Financial District'): 17,
    ('Alamo Square', 'Nob Hill'): 11,
    ('Alamo Square', 'Sunset District'): 16,
    ('Alamo Square', 'Chinatown'): 15,
    ('Alamo Square', 'Russian Hill'): 13,
    ('Alamo Square', 'North Beach'): 15,
    ('Alamo Square', 'Haight-Ashbury'): 5,
    ('Marina District', 'Union Square'): 16,
    ('Marina District', 'Presidio'): 10,
    ('Marina District', 'Alamo Square'): 15,
    ('Marina District', 'Financial District'): 17,
    ('Marina District', 'Nob Hill'): 12,
    ('Marina District', 'Sunset District'): 19,
    ('Marina District', 'Chinatown'): 15,
    ('Marina District', 'Russian Hill'): 8,
    ('Marina District', 'North Beach'): 11,
    ('Marina District', 'Haight-Ashbury'): 16,
    ('Financial District', 'Union Square'): 9,
    ('Financial District', 'Presidio'): 22,
    ('Financial District', 'Alamo Square'): 17,
    ('Financial District', 'Marina District'): 15,
    ('Financial District', 'Nob Hill'): 8,
    ('Financial District', 'Sunset District'): 30,
    ('Financial District', 'Chinatown'): 5,
    ('Financial District', 'Russian Hill'): 11,
    ('Financial District', 'North Beach'): 7,
    ('Financial District', 'Haight-Ashbury'): 19,
    ('Nob Hill', 'Union Square'): 7,
    ('Nob Hill', 'Presidio'): 17,
    ('Nob Hill', 'Alamo Square'): 11,
    ('Nob Hill', 'Marina District'): 11,
    ('Nob Hill', 'Financial District'): 9,
    ('Nob Hill', 'Sunset District'): 24,
    ('Nob Hill', 'Chinatown'): 6,
    ('Nob Hill', 'Russian Hill'): 5,
    ('Nob Hill', 'North Beach'): 8,
    ('Nob Hill', 'Haight-Ashbury'): 13,
    ('Sunset District', 'Union Square'): 30,
    ('Sunset District', 'Presidio'): 16,
    ('Sunset District', 'Alamo Square'): 17,
    ('Sunset District', 'Marina District'): 21,
    ('Sunset District', 'Financial District'): 30,
    ('Sunset District', 'Nob Hill'): 27,
    ('Sunset District', 'Chinatown'): 30,
    ('Sunset District', 'Russian Hill'): 24,
    ('Sunset District', 'North Beach'): 28,
    ('Sunset District', 'Haight-Ashbury'): 15,
    ('Chinatown', 'Union Square'): 7,
    ('Chinatown', 'Presidio'): 19,
    ('Chinatown', 'Alamo Square'): 17,
    ('Chinatown', 'Marina District'): 12,
    ('Chinatown', 'Financial District'): 5,
    ('Chinatown', 'Nob Hill'): 9,
    ('Chinatown', 'Sunset District'): 29,
    ('Chinatown', 'Russian Hill'): 7,
    ('Chinatown', 'North Beach'): 3,
    ('Chinatown', 'Haight-Ashbury'): 19,
    ('Russian Hill', 'Union Square'): 10,
    ('Russian Hill', 'Presidio'): 14,
    ('Russian Hill', 'Alamo Square'): 15,
    ('Russian Hill', 'Marina District'): 7,
    ('Russian Hill', 'Financial District'): 11,
    ('Russian Hill', 'Nob Hill'): 5,
    ('Russian Hill', 'Sunset District'): 23,
    ('Russian Hill', 'Chinatown'): 9,
    ('Russian Hill', 'North Beach'): 5,
    ('Russian Hill', 'Haight-Ashbury'): 17,
    ('North Beach', 'Union Square'): 7,
    ('North Beach', 'Presidio'): 17,
    ('North Beach', 'Alamo Square'): 16,
    ('North Beach', 'Marina District'): 9,
    ('North Beach', 'Financial District'): 8,
    ('North Beach', 'Nob Hill'): 7,
    ('North Beach', 'Sunset District'): 27,
    ('North Beach', 'Chinatown'): 6,
    ('North Beach', 'Russian Hill'): 4,
    ('North Beach', 'Haight-Ashbury'): 18,
    ('Haight-Ashbury', 'Union Square'): 19,
    ('Haight-Ashbury', 'Presidio'): 15,
    ('Haight-Ashbury', 'Alamo Square'): 5,
    ('Haight-Ashbury', 'Marina District'): 17,
    ('Haight-Ashbury', 'Financial District'): 21,
    ('Haight-Ashbury', 'Nob Hill'): 15,
    ('Haight-Ashbury', 'Sunset District'): 15,
    ('Haight-Ashbury', 'Chinatown'): 19,
    ('Haight-Ashbury', 'Russian Hill'): 17,
    ('Haight-Ashbury', 'North Beach'): 19,
}

friends = [
    {
        'name': 'Kimberly',
        'location': 'Presidio',
        'start_time': 15 * 60 + 30,  # 3:30 PM
        'end_time': 16 * 60 + 0,     # 4:00 PM
        'duration': 15
    },
    {
        'name': 'Elizabeth',
        'location': 'Alamo Square',
        'start_time': 19 * 60 + 15,  # 7:15 PM
        'end_time': 20 * 60 + 15,    # 8:15 PM
        'duration': 15
    },
    {
        'name': 'Joshua',
        'location': 'Marina District',
        'start_time': 10 * 60 + 30,  # 10:30 AM
        'end_time': 14 * 60 + 15,    # 2:15 PM
        'duration': 45
    },
    {
        'name': 'Sandra',
        'location': 'Financial District',
        'start_time': 19 * 60 + 30,  # 7:30 PM
        'end_time': 20 * 60 + 15,    # 8:15 PM
        'duration': 45
    },
    {
        'name': 'Kenneth',
        'location': 'Nob Hill',
        'start_time': 12 * 60 + 45,  # 12:45 PM
        'end_time': 21 * 60 + 45,    # 9:45 PM
        'duration': 30
    },
    {
        'name': 'Betty',
        'location': 'Sunset District',
        'start_time': 14 * 60 + 0,   # 2:00 PM
        'end_time': 19 * 60 + 0,     # 7:00 PM
        'duration': 60
    },
    {
        'name': 'Deborah',
        'location': 'Chinatown',
        'start_time': 17 * 60 + 15,  # 5:15 PM
        'end_time': 20 * 60 + 30,    # 8:30 PM
        'duration': 15
    },
    {
        'name': 'Barbara',
        'location': 'Russian Hill',
        'start_time': 17 * 60 + 30,  # 5:30 PM
        'end_time': 21 * 60 + 15,    # 9:15 PM
        'duration': 120
    },
    {
        'name': 'Steven',
        'location': 'North Beach',
        'start_time': 17 * 60 + 45,  # 5:45 PM
        'end_time': 20 * 60 + 45,    # 8:45 PM
        'duration': 90
    },
    {
        'name': 'Daniel',
        'location': 'Haight-Ashbury',
        'start_time': 18 * 60 + 30,  # 6:30 PM
        'end_time': 18 * 60 + 45,    # 6:45 PM
        'duration': 15
    },
]

def convert_minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

best_itinerary = []
max_met = 0

for perm in itertools.permutations(friends):
    current_time = 540  # 9:00 AM
    current_location = 'Union Square'
    itinerary = []
    for friend in perm:
        travel_time = travel_times.get((current_location, friend['location']), None)
        if travel_time is None:
            break
        arrival_time = current_time + travel_time
        meeting_start = max(arrival_time, friend['start_time'])
        meeting_end = meeting_start + friend['duration']
        if meeting_end > friend['end_time']:
            break
        itinerary.append({
            'action': 'meet',
            'location': friend['location'],
            'person': friend['name'],
            'start_time': convert_minutes_to_time(meeting_start),
            'end_time': convert_minutes_to_time(meeting_end)
        })
        current_time = meeting_end
        current_location = friend['location']
    if len(itinerary) > max_met:
        max_met = len(itinerary)
        best_itinerary = itinerary

output = {
    "itinerary": best_itinerary
}

print(json.dumps(output, indent=2))