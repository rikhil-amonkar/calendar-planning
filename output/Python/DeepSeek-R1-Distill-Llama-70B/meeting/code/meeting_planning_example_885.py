import json
from itertools import permutations

def time_to_minutes(time_str):
    hours, mins = map(int, time_str.split(':'))
    return hours * 60 + mins

def minutes_to_time(mins):
    hours = mins // 60
    mins = mins % 60
    return f"{hours}:{mins:02d}"

travel_times = {
    ('Russian Hill', 'Marina District'): 7,
    ('Russian Hill', 'Financial District'): 11,
    ('Russian Hill', 'Alamo Square'): 15,
    ('Russian Hill', 'Golden Gate Park'): 21,
    ('Russian Hill', 'The Castro'): 21,
    ('Russian Hill', 'Bayview'): 23,
    ('Russian Hill', 'Sunset District'): 23,
    ('Russian Hill', 'Haight-Ashbury'): 17,
    ('Russian Hill', 'Nob Hill'): 5,
    ('Marina District', 'Russian Hill'): 8,
    ('Marina District', 'Financial District'): 17,
    ('Marina District', 'Alamo Square'): 15,
    ('Marina District', 'Golden Gate Park'): 18,
    ('Marina District', 'The Castro'): 22,
    ('Marina District', 'Bayview'): 27,
    ('Marina District', 'Sunset District'): 19,
    ('Marina District', 'Haight-Ashbury'): 16,
    ('Marina District', 'Nob Hill'): 12,
    ('Financial District', 'Russian Hill'): 11,
    ('Financial District', 'Marina District'): 15,
    ('Financial District', 'Alamo Square'): 17,
    ('Financial District', 'Golden Gate Park'): 23,
    ('Financial District', 'The Castro'): 20,
    ('Financial District', 'Bayview'): 19,
    ('Financial District', 'Sunset District'): 30,
    ('Financial District', 'Haight-Ashbury'): 19,
    ('Financial District', 'Nob Hill'): 8,
    ('Alamo Square', 'Russian Hill'): 13,
    ('Alamo Square', 'Marina District'): 15,
    ('Alamo Square', 'Financial District'): 17,
    ('Alamo Square', 'Golden Gate Park'): 9,
    ('Alamo Square', 'The Castro'): 8,
    ('Alamo Square', 'Bayview'): 16,
    ('Alamo Square', 'Sunset District'): 16,
    ('Alamo Square', 'Haight-Ashbury'): 5,
    ('Alamo Square', 'Nob Hill'): 11,
    ('Golden Gate Park', 'Russian Hill'): 19,
    ('Golden Gate Park', 'Marina District'): 16,
    ('Golden Gate Park', 'Financial District'): 26,
    ('Golden Gate Park', 'Alamo Square'): 9,
    ('Golden Gate Park', 'The Castro'): 13,
    ('Golden Gate Park', 'Bayview'): 23,
    ('Golden Gate Park', 'Sunset District'): 10,
    ('Golden Gate Park', 'Haight-Ashbury'): 7,
    ('Golden Gate Park', 'Nob Hill'): 20,
    ('The Castro', 'Russian Hill'): 18,
    ('The Castro', 'Marina District'): 21,
    ('The Castro', 'Financial District'): 21,
    ('The Castro', 'Alamo Square'): 8,
    ('The Castro', 'Golden Gate Park'): 11,
    ('The Castro', 'Bayview'): 19,
    ('The Castro', 'Sunset District'): 17,
    ('The Castro', 'Haight-Ashbury'): 6,
    ('The Castro', 'Nob Hill'): 16,
    ('Bayview', 'Russian Hill'): 23,
    ('Bayview', 'Marina District'): 27,
    ('Bayview', 'Financial District'): 19,
    ('Bayview', 'Alamo Square'): 16,
    ('Bayview', 'Golden Gate Park'): 22,
    ('Bayview', 'The Castro'): 19,
    ('Bayview', 'Sunset District'): 23,
    ('Bayview', 'Haight-Ashbury'): 19,
    ('Bayview', 'Nob Hill'): 20,
    ('Sunset District', 'Russian Hill'): 24,
    ('Sunset District', 'Marina District'): 21,
    ('Sunset District', 'Financial District'): 30,
    ('Sunset District', 'Alamo Square'): 17,
    ('Sunset District', 'Golden Gate Park'): 11,
    ('Sunset District', 'The Castro'): 17,
    ('Sunset District', 'Bayview'): 22,
    ('Sunset District', 'Haight-Ashbury'): 15,
    ('Sunset District', 'Nob Hill'): 27,
    ('Haight-Ashbury', 'Russian Hill'): 17,
    ('Haight-Ashbury', 'Marina District'): 17,
    ('Haight-Ashbury', 'Financial District'): 21,
    ('Haight-Ashbury', 'Alamo Square'): 5,
    ('Haight-Ashbury', 'Golden Gate Park'): 7,
    ('Haight-Ashbury', 'The Castro'): 6,
    ('Haight-Ashbury', 'Bayview'): 18,
    ('Haight-Ashbury', 'Sunset District'): 15,
    ('Haight-Ashbury', 'Nob Hill'): 15,
    ('Nob Hill', 'Russian Hill'): 5,
    ('Nob Hill', 'Marina District'): 11,
    ('Nob Hill', 'Financial District'): 9,
    ('Nob Hill', 'Alamo Square'): 11,
    ('Nob Hill', 'Golden Gate Park'): 17,
    ('Nob Hill', 'The Castro'): 17,
    ('Nob Hill', 'Bayview'): 19,
    ('Nob Hill', 'Sunset District'): 24,
    ('Nob Hill', 'Haight-Ashbury'): 13
}

friends = [
    {
        'name': 'Mark',
        'location': 'Marina District',
        'available_start': '18:45',
        'available_end': '21:00',
        'required_duration': 90
    },
    {
        'name': 'Karen',
        'location': 'Financial District',
        'available_start': '09:30',
        'available_end': '12:45',
        'required_duration': 90
    },
    {
        'name': 'Barbara',
        'location': 'Alamo Square',
        'available_start': '10:00',
        'available_end': '19:30',
        'required_duration': 90
    },
    {
        'name': 'Nancy',
        'location': 'Golden Gate Park',
        'available_start': '16:45',
        'available_end': '20:00',
        'required_duration': 105
    },
    {
        'name': 'David',
        'location': 'The Castro',
        'available_start': '09:00',
        'available_end': '18:00',
        'required_duration': 120
    },
    {
        'name': 'Linda',
        'location': 'Bayview',
        'available_start': '18:15',
        'available_end': '19:45',
        'required_duration': 45
    },
    {
        'name': 'Kevin',
        'location': 'Sunset District',
        'available_start': '10:00',
        'available_end': '17:45',
        'required_duration': 120
    },
    {
        'name': 'Matthew',
        'location': 'Haight-Ashbury',
        'available_start': '10:15',
        'available_end': '15:30',
        'required_duration': 45
    },
    {
        'name': 'Andrew',
        'location': 'Nob Hill',
        'available_start': '11:45',
        'available_end': '16:45',
        'required_duration': 105
    }
]

current_time = 540  # 9:00 AM in minutes
current_location = 'Russian Hill'

best_itinerary = []

for perm in permutations(friends):
    itinerary = []
    temp_time = current_time
    temp_loc = current_location
    valid = True

    for friend in perm:
        travel = travel_times.get((temp_loc, friend['location']), None)
        if travel is None:
            valid = False
            break
        arrival_time = temp_time + travel

        avail_start = time_to_minutes(friend['available_start'])
        avail_end = time_to_minutes(friend['available_end'])

        start_time = max(arrival_time, avail_start)
        end_time = start_time + friend['required_duration']

        if end_time > avail_end:
            valid = False
            break

        itinerary.append({
            'action': 'meet',
            'location': friend['location'],
            'person': friend['name'],
            'start_time': minutes_to_time(start_time),
            'end_time': minutes_to_time(end_time)
        })

        temp_time = end_time
        temp_loc = friend['location']

    if valid and len(itinerary) > len(best_itinerary):
        best_itinerary = itinerary

result = {'itinerary': best_itinerary}
print(json.dumps(result))