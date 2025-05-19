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
    ('Embarcadero', 'Bayview'): 21,
    ('Embarcadero', 'Chinatown'): 7,
    ('Embarcadero', 'Alamo Square'): 19,
    ('Embarcadero', 'Nob Hill'): 10,
    ('Embarcadero', 'Presidio'): 20,
    ('Embarcadero', 'Union Square'): 10,
    ('Embarcadero', 'The Castro'): 25,
    ('Embarcadero', 'North Beach'): 5,
    ('Embarcadero', 'Fisherman\'s Wharf'): 6,
    ('Embarcadero', 'Marina District'): 12,
    ('Bayview', 'Embarcadero'): 19,
    ('Bayview', 'Chinatown'): 19,
    ('Bayview', 'Alamo Square'): 16,
    ('Bayview', 'Nob Hill'): 20,
    ('Bayview', 'Presidio'): 32,
    ('Bayview', 'Union Square'): 18,
    ('Bayview', 'The Castro'): 19,
    ('Bayview', 'North Beach'): 22,
    ('Bayview', 'Fisherman\'s Wharf'): 25,
    ('Bayview', 'Marina District'): 27,
    ('Chinatown', 'Embarcadero'): 5,
    ('Chinatown', 'Bayview'): 20,
    ('Chinatown', 'Alamo Square'): 17,
    ('Chinatown', 'Nob Hill'): 9,
    ('Chinatown', 'Presidio'): 19,
    ('Chinatown', 'Union Square'): 7,
    ('Chinatown', 'The Castro'): 22,
    ('Chinatown', 'North Beach'): 3,
    ('Chinatown', 'Fisherman\'s Wharf'): 8,
    ('Chinatown', 'Marina District'): 12,
    ('Alamo Square', 'Embarcadero'): 16,
    ('Alamo Square', 'Bayview'): 16,
    ('Alamo Square', 'Chinatown'): 15,
    ('Alamo Square', 'Nob Hill'): 11,
    ('Alamo Square', 'Presidio'): 17,
    ('Alamo Square', 'Union Square'): 14,
    ('Alamo Square', 'The Castro'): 8,
    ('Alamo Square', 'North Beach'): 15,
    ('Alamo Square', 'Fisherman\'s Wharf'): 19,
    ('Alamo Square', 'Marina District'): 15,
    ('Nob Hill', 'Embarcadero'): 9,
    ('Nob Hill', 'Bayview'): 19,
    ('Nob Hill', 'Chinatown'): 6,
    ('Nob Hill', 'Alamo Square'): 11,
    ('Nob Hill', 'Presidio'): 17,
    ('Nob Hill', 'Union Square'): 7,
    ('Nob Hill', 'The Castro'): 17,
    ('Nob Hill', 'North Beach'): 8,
    ('Nob Hill', 'Fisherman\'s Wharf'): 10,
    ('Nob Hill', 'Marina District'): 11,
    ('Presidio', 'Embarcadero'): 20,
    ('Presidio', 'Bayview'): 31,
    ('Presidio', 'Chinatown'): 21,
    ('Presidio', 'Alamo Square'): 19,
    ('Presidio', 'Nob Hill'): 18,
    ('Presidio', 'Union Square'): 22,
    ('Presidio', 'The Castro'): 21,
    ('Presidio', 'North Beach'): 18,
    ('Presidio', 'Fisherman\'s Wharf'): 19,
    ('Presidio', 'Marina District'): 11,
    ('Union Square', 'Embarcadero'): 11,
    ('Union Square', 'Bayview'): 15,
    ('Union Square', 'Chinatown'): 7,
    ('Union Square', 'Alamo Square'): 15,
    ('Union Square', 'Nob Hill'): 9,
    ('Union Square', 'Presidio'): 24,
    ('Union Square', 'The Castro'): 17,
    ('Union Square', 'North Beach'): 10,
    ('Union Square', 'Fisherman\'s Wharf'): 15,
    ('Union Square', 'Marina District'): 18,
    ('The Castro', 'Embarcadero'): 22,
    ('The Castro', 'Bayview'): 19,
    ('The Castro', 'Chinatown'): 22,
    ('The Castro', 'Alamo Square'): 8,
    ('The Castro', 'Nob Hill'): 16,
    ('The Castro', 'Presidio'): 20,
    ('The Castro', 'Union Square'): 19,
    ('The Castro', 'North Beach'): 20,
    ('The Castro', 'Fisherman\'s Wharf'): 24,
    ('The Castro', 'Marina District'): 21,
    ('North Beach', 'Embarcadero'): 6,
    ('North Beach', 'Bayview'): 25,
    ('North Beach', 'Chinatown'): 6,
    ('North Beach', 'Alamo Square'): 16,
    ('North Beach', 'Nob Hill'): 7,
    ('North Beach', 'Presidio'): 17,
    ('North Beach', 'Union Square'): 7,
    ('North Beach', 'The Castro'): 23,
    ('North Beach', 'Fisherman\'s Wharf'): 5,
    ('North Beach', 'Marina District'): 9,
    ('Fisherman\'s Wharf', 'Embarcadero'): 8,
    ('Fisherman\'s Wharf', 'Bayview'): 26,
    ('Fisherman\'s Wharf', 'Chinatown'): 12,
    ('Fisherman\'s Wharf', 'Alamo Square'): 21,
    ('Fisherman\'s Wharf', 'Nob Hill'): 11,
    ('Fisherman\'s Wharf', 'Presidio'): 17,
    ('Fisherman\'s Wharf', 'Union Square'): 13,
    ('Fisherman\'s Wharf', 'The Castro'): 27,
    ('Fisherman\'s Wharf', 'North Beach'): 6,
    ('Fisherman\'s Wharf', 'Marina District'): 9,
    ('Marina District', 'Embarcadero'): 14,
    ('Marina District', 'Bayview'): 27,
    ('Marina District', 'Chinatown'): 15,
    ('Marina District', 'Alamo Square'): 15,
    ('Marina District', 'Nob Hill'): 12,
    ('Marina District', 'Presidio'): 10,
    ('Marina District', 'Union Square'): 16,
    ('Marina District', 'The Castro'): 22,
    ('Marina District', 'North Beach'): 11,
    ('Marina District', 'Fisherman\'s Wharf'): 10
}

friends = [
    {
        'name': 'Matthew',
        'location': 'Bayview',
        'available_start': '19:15',
        'available_end': '22:00',
        'required_duration': 120
    },
    {
        'name': 'Karen',
        'location': 'Chinatown',
        'available_start': '19:15',
        'available_end': '21:15',
        'required_duration': 90
    },
    {
        'name': 'Sarah',
        'location': 'Alamo Square',
        'available_start': '20:00',
        'available_end': '21:45',
        'required_duration': 105
    },
    {
        'name': 'Jessica',
        'location': 'Nob Hill',
        'available_start': '16:30',
        'available_end': '18:45',
        'required_duration': 120
    },
    {
        'name': 'Stephanie',
        'location': 'Presidio',
        'available_start': '07:30',
        'available_end': '10:15',
        'required_duration': 60
    },
    {
        'name': 'Mary',
        'location': 'Union Square',
        'available_start': '16:45',
        'available_end': '21:30',
        'required_duration': 60
    },
    {
        'name': 'Charles',
        'location': 'The Castro',
        'available_start': '16:30',
        'available_end': '22:00',
        'required_duration': 105
    },
    {
        'name': 'Nancy',
        'location': 'North Beach',
        'available_start': '14:45',
        'available_end': '20:00',
        'required_duration': 15
    },
    {
        'name': 'Thomas',
        'location': 'Fisherman\'s Wharf',
        'available_start': '13:30',
        'available_end': '19:00',
        'required_duration': 30
    },
    {
        'name': 'Brian',
        'location': 'Marina District',
        'available_start': '12:15',
        'available_end': '18:00',
        'required_duration': 60
    }
]

current_time = 540  # 9:00 AM in minutes
current_location = 'Embarcadero'

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