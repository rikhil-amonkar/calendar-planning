import sys
from functools import lru_cache
import json

def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

# Define friends
friends = [
    {
        'name': 'Charles',
        'location': 'Presidio',
        'available_start': 795,  # 1:15 PM
        'available_end': 900,    # 3:00 PM
        'required_duration': 105,
        'index': 0
    },
    {
        'name': 'Robert',
        'location': 'Nob Hill',
        'available_start': 795,  # 1:15 PM
        'available_end': 1050,   # 5:30 PM
        'required_duration': 90,
        'index': 1
    },
    {
        'name': 'Nancy',
        'location': 'Pacific Heights',
        'available_start': 1005,  # 2:45 PM
        'available_end': 1320,    # 10:00 PM
        'required_duration': 105,
        'index': 2
    },
    {
        'name': 'Brian',
        'location': 'Mission District',
        'available_start': 930,   # 3:30 PM
        'available_end': 1320,    # 10:00 PM
        'required_duration': 60,
        'index': 3
    },
    {
        'name': 'Kimberly',
        'location': 'Marina District',
        'available_start': 1020,  # 5:00 PM
        'available_end': 1185,    # 7:45 PM
        'required_duration': 75,
        'index': 4
    },
    {
        'name': 'David',
        'location': 'North Beach',
        'available_start': 885,   # 2:45 PM
        'available_end': 990,     # 4:30 PM
        'required_duration': 75,
        'index': 5
    },
    {
        'name': 'William',
        'location': 'Russian Hill',
        'available_start': 750,   # 12:30 PM
        'available_end': 1155,    # 7:15 PM
        'required_duration': 120,
        'index': 6
    },
    {
        'name': 'Jeffrey',
        'location': 'Richmond District',
        'available_start': 720,   # 12:00 PM
        'available_end': 1155,    # 7:15 PM
        'required_duration': 45,
        'index': 7
    },
    {
        'name': 'Karen',
        'location': 'Embarcadero',
        'available_start': 855,   # 2:15 PM
        'available_end': 1245,    # 8:45 PM
        'required_duration': 60,
        'index': 8
    },
    {
        'name': 'Joshua',
        'location': 'Alamo Square',
        'available_start': 1125,  # 6:45 PM
        'available_end': 1320,    # 10:00 PM
        'required_duration': 60,
        'index': 9
    }
]

# Define travel times between locations
travel_time = {
    'Sunset District': {
        'Presidio': 16,
        'Nob Hill': 27,
        'Pacific Heights': 21,
        'Mission District': 25,
        'Marina District': 21,
        'North Beach': 28,
        'Russian Hill': 24,
        'Richmond District': 12,
        'Embarcadero': 30,
        'Alamo Square': 17
    },
    'Presidio': {
        'Sunset District': 15,
        'Nob Hill': 18,
        'Pacific Heights': 11,
        'Mission District': 26,
        'Marina District': 11,
        'North Beach': 18,
        'Russian Hill': 14,
        'Richmond District': 7,
        'Embarcadero': 20,
        'Alamo Square': 19
    },
    'Nob Hill': {
        'Sunset District': 24,
        'Presidio': 17,
        'Pacific Heights': 8,
        'Mission District': 13,
        'Marina District': 11,
        'North Beach': 8,
        'Russian Hill': 5,
        'Richmond District': 14,
        'Embarcadero': 9,
        'Alamo Square': 11
    },
    'Pacific Heights': {
        'Sunset District': 21,
        'Presidio': 11,
        'Nob Hill': 8,
        'Mission District': 15,
        'Marina District': 6,
        'North Beach': 9,
        'Russian Hill': 7,
        'Richmond District': 12,
        'Embarcadero': 10,
        'Alamo Square': 10
    },
    'Mission District': {
        'Sunset District': 24,
        'Presidio': 25,
        'Nob Hill': 12,
        'Pacific Heights': 16,
        'Marina District': 19,
        'North Beach': 17,
        'Russian Hill': 15,
        'Richmond District': 20,
        'Embarcadero': 19,
        'Alamo Square': 11
    },
    'Marina District': {
        'Sunset District': 19,
        'Presidio': 10,
        'Nob Hill': 12,
        'Pacific Heights': 7,
        'Mission District': 20,
        'North Beach': 11,
        'Russian Hill': 8,
        'Richmond District': 11,
        'Embarcadero': 14,
        'Alamo Square': 15
    },
    'North Beach': {
        'Sunset District': 27,
        'Presidio': 17,
        'Nob Hill': 7,
        'Pacific Heights': 8,
        'Mission District': 18,
        'Marina District': 9,
        'Russian Hill': 4,
        'Richmond District': 18,
        'Embarcadero': 6,
        'Alamo Square': 16
    },
    'Russian Hill': {
        'Sunset District': 23,
        'Presidio': 14,
        'Nob Hill': 5,
        'Pacific Heights': 7,
        'Mission District': 16,
        'Marina District': 7,
        'North Beach': 5,
        'Richmond District': 14,
        'Embarcadero': 8,
        'Alamo Square': 15
    },
    'Richmond District': {
        'Sunset District': 11,
        'Presidio': 7,
        'Nob Hill': 17,
        'Pacific Heights': 10,
        'Mission District': 20,
        'Marina District': 9,
        'North Beach': 17,
        'Russian Hill': 13,
        'Embarcadero': 19,
        'Alamo Square': 13
    },
    'Embarcadero': {
        'Sunset District': 30,
        'Presidio': 20,
        'Nob Hill': 10,
        'Pacific Heights': 11,
        'Mission District': 20,
        'Marina District': 12,
        'North Beach': 5,
        'Russian Hill': 8,
        'Richmond District': 21,
        'Alamo Square': 19
    },
    'Alamo Square': {
        'Sunset District': 16,
        'Presidio': 17,
        'Nob Hill': 11,
        'Pacific Heights': 10,
        'Mission District': 10,
        'Marina District': 15,
        'North Beach': 15,
        'Russian Hill': 13,
        'Richmond District': 11,
        'Embarcadero': 16
    }
}

@lru_cache(maxsize=None)
def find_optimal(current_time, current_location, visited_mask):
    max_count = 0
    best_itinerary = []

    for friend in friends:
        if visited_mask & (1 << friend['index']):
            continue
        if current_location not in travel_time or friend['location'] not in travel_time[current_location]:
            continue
        travel_minutes = travel_time[current_location][friend['location']]
        arrival_time = current_time + travel_minutes
        earliest_start = max(friend['available_start'], arrival_time)
        if earliest_start + friend['required_duration'] > friend['available_end']:
            continue
        new_time = earliest_start + friend['required_duration']
        new_mask = visited_mask | (1 << friend['index'])
        count, sub_itinerary = find_optimal(new_time, friend['location'], new_mask)
        total_count = 1 + count
        if total_count > max_count:
            max_count = total_count
            meeting = {
                'action': 'meet',
                'location': friend['location'],
                'person': friend['name'],
                'start_time': minutes_to_time(earliest_start),
                'end_time': minutes_to_time(earliest_start + friend['required_duration'])
            }
            best_itinerary = [meeting] + sub_itinerary

    return (max_count, best_itinerary)

# Initial call: 9:00 AM at Sunset District
max_count, itinerary = find_optimal(540, 'Sunset District', 0)

result = {"itinerary": itinerary}
print(json.dumps(result, indent=2))