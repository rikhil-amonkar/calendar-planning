import itertools
import json

def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

travel_times = {
    ('Financial District', 'Chinatown'): 5,
    ('Financial District', 'Alamo Square'): 17,
    ('Financial District', 'Bayview'): 19,
    ('Financial District', 'Fisherman\'s Wharf'): 10,
    ('Chinatown', 'Financial District'): 5,
    ('Chinatown', 'Alamo Square'): 17,
    ('Chinatown', 'Bayview'): 22,
    ('Chinatown', 'Fisherman\'s Wharf'): 8,
    ('Alamo Square', 'Financial District'): 17,
    ('Alamo Square', 'Chinatown'): 16,
    ('Alamo Square', 'Bayview'): 16,
    ('Alamo Square', 'Fisherman\'s Wharf'): 19,
    ('Bayview', 'Financial District'): 19,
    ('Bayview', 'Chinatown'): 18,
    ('Bayview', 'Alamo Square'): 16,
    ('Bayview', 'Fisherman\'s Wharf'): 25,
    ('Fisherman\'s Wharf', 'Financial District'): 11,
    ('Fisherman\'s Wharf', 'Chinatown'): 12,
    ('Fisherman\'s Wharf', 'Alamo Square'): 20,
    ('Fisherman\'s Wharf', 'Bayview'): 26,
}

friends = [
    {
        'name': 'Nancy',
        'location': 'Chinatown',
        'earliest_available': 570,  # 9:30 AM
        'latest_available': 810,    # 1:30 PM
        'required_duration': 90
    },
    {
        'name': 'Mary',
        'location': 'Alamo Square',
        'earliest_available': 420,  # 7:00 AM
        'latest_available': 1260,   # 9:00 PM
        'required_duration': 75
    },
    {
        'name': 'Jessica',
        'location': 'Bayview',
        'earliest_available': 675,  # 11:15 AM
        'latest_available': 825,    # 1:45 PM
        'required_duration': 45
    }
]

for perm in itertools.permutations(friends):
    current_time = 540  # 9:00 AM in minutes
    current_location = 'Financial District'
    itinerary = []
    valid = True
    for friend in perm:
        travel_key = (current_location, friend['location'])
        if travel_key not in travel_times:
            valid = False
            break
        travel_time = travel_times[travel_key]
        arrival_time = current_time + travel_time
        earliest_start = max(arrival_time, friend['earliest_available'])
        required_end = earliest_start + friend['required_duration']
        if required_end > friend['latest_available']:
            valid = False
            break
        itinerary.append({
            'action': 'meet',
            'location': friend['location'],
            'person': friend['name'],
            'start_time': minutes_to_time(earliest_start),
            'end_time': minutes_to_time(required_end)
        })
        current_time = required_end
        current_location = friend['location']
    if valid:
        result = {"itinerary": itinerary}
        print(json.dumps(result))
        break