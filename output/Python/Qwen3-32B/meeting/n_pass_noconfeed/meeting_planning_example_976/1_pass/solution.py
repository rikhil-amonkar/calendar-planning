import json
from copy import deepcopy

def to_minutes(time_str):
    hour_str, minute_period = time_str.split(':')
    hour = int(hour_str)
    minute = int(minute_period[:-2])
    period = minute_period[-2:].upper()
    if period == 'PM' and hour != 12:
        hour += 12
    elif period == 'AM' and hour == 12:
        hour = 0
    return hour * 60 + minute

def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

travel_times = {
    'Embarcadero': {
        'Bayview': 21,
        'Chinatown': 7,
        'Alamo Square': 19,
        'Nob Hill': 10,
        'Presidio': 20,
        'Union Square': 10,
        'The Castro': 25,
        'North Beach': 5,
        'Fisherman\'s Wharf': 6,
        'Marina District': 12,
    },
    'Bayview': {
        'Embarcadero': 19,
        'Chinatown': 19,
        'Alamo Square': 16,
        'Nob Hill': 20,
        'Presidio': 32,
        'Union Square': 18,
        'The Castro': 19,
        'North Beach': 22,
        'Fisherman\'s Wharf': 25,
        'Marina District': 27,
    },
    'Chinatown': {
        'Embarcadero': 5,
        'Bayview': 20,
        'Alamo Square': 17,
        'Nob Hill': 9,
        'Presidio': 19,
        'Union Square': 7,
        'The Castro': 22,
        'North Beach': 3,
        'Fisherman\'s Wharf': 8,
        'Marina District': 12,
    },
    'Alamo Square': {
        'Embarcadero': 16,
        'Bayview': 16,
        'Chinatown': 15,
        'Nob Hill': 11,
        'Presidio': 17,
        'Union Square': 14,
        'The Castro': 8,
        'North Beach': 15,
        'Fisherman\'s Wharf': 19,
        'Marina District': 15,
    },
    'Nob Hill': {
        'Embarcadero': 9,
        'Bayview': 19,
        'Chinatown': 6,
        'Alamo Square': 11,
        'Presidio': 17,
        'Union Square': 7,
        'The Castro': 17,
        'North Beach': 8,
        'Fisherman\'s Wharf': 10,
        'Marina District': 11,
    },
    'Presidio': {
        'Embarcadero': 20,
        'Bayview': 31,
        'Chinatown': 21,
        'Alamo Square': 19,
        'Nob Hill': 18,
        'Union Square': 22,
        'The Castro': 21,
        'North Beach': 18,
        'Fisherman\'s Wharf': 19,
        'Marina District': 11,
    },
    'Union Square': {
        'Embarcadero': 11,
        'Bayview': 15,
        'Chinatown': 7,
        'Alamo Square': 15,
        'Nob Hill': 9,
        'Presidio': 24,
        'The Castro': 17,
        'North Beach': 10,
        'Fisherman\'s Wharf': 15,
        'Marina District': 18,
    },
    'The Castro': {
        'Embarcadero': 22,
        'Bayview': 19,
        'Chinatown': 22,
        'Alamo Square': 8,
        'Nob Hill': 16,
        'Presidio': 20,
        'Union Square': 19,
        'North Beach': 20,
        'Fisherman\'s Wharf': 24,
        'Marina District': 21,
    },
    'North Beach': {
        'Embarcadero': 6,
        'Bayview': 25,
        'Chinatown': 6,
        'Alamo Square': 16,
        'Nob Hill': 7,
        'Presidio': 17,
        'Union Square': 7,
        'The Castro': 23,
        'Fisherman\'s Wharf': 5,
        'Marina District': 9,
    },
    'Fisherman\'s Wharf': {
        'Embarcadero': 8,
        'Bayview': 26,
        'Chinatown': 12,
        'Alamo Square': 21,
        'Nob Hill': 11,
        'Presidio': 17,
        'Union Square': 13,
        'The Castro': 27,
        'North Beach': 6,
        'Marina District': 9,
    },
    'Marina District': {
        'Embarcadero': 14,
        'Bayview': 27,
        'Chinatown': 15,
        'Alamo Square': 15,
        'Nob Hill': 12,
        'Presidio': 10,
        'Union Square': 16,
        'The Castro': 22,
        'North Beach': 11,
        'Fisherman\'s Wharf': 10,
    },
}

friends = [
    {
        'name': 'Stephanie',
        'location': 'Presidio',
        'available_start': to_minutes('7:30AM'),
        'available_end': to_minutes('10:15AM'),
        'min_duration': 60,
    },
    {
        'name': 'Nancy',
        'location': 'North Beach',
        'available_start': to_minutes('2:45PM'),
        'available_end': to_minutes('8:00PM'),
        'min_duration': 15,
    },
    {
        'name': 'Thomas',
        'location': 'Fisherman\'s Wharf',
        'available_start': to_minutes('1:30PM'),
        'available_end': to_minutes('7:00PM'),
        'min_duration': 30,
    },
    {
        'name': 'Brian',
        'location': 'Marina District',
        'available_start': to_minutes('12:15PM'),
        'available_end': to_minutes('6:00PM'),
        'min_duration': 60,
    },
    {
        'name': 'Jessica',
        'location': 'Nob Hill',
        'available_start': to_minutes('4:30PM'),
        'available_end': to_minutes('6:45PM'),
        'min_duration': 120,
    },
    {
        'name': 'Mary',
        'location': 'Union Square',
        'available_start': to_minutes('4:45PM'),
        'available_end': to_minutes('9:30PM'),
        'min_duration': 60,
    },
    {
        'name': 'Charles',
        'location': 'The Castro',
        'available_start': to_minutes('4:30PM'),
        'available_end': to_minutes('10:00PM'),
        'min_duration': 105,
    },
    {
        'name': 'Matthew',
        'location': 'Bayview',
        'available_start': to_minutes('7:15PM'),
        'available_end': to_minutes('10:00PM'),
        'min_duration': 120,
    },
    {
        'name': 'Karen',
        'location': 'Chinatown',
        'available_start': to_minutes('7:15PM'),
        'available_end': to_minutes('9:15PM'),
        'min_duration': 90,
    },
    {
        'name': 'Sarah',
        'location': 'Alamo Square',
        'available_start': to_minutes('8:00PM'),
        'available_end': to_minutes('9:45PM'),
        'min_duration': 105,
    },
]

best_itinerary = []
best_length = 0

def backtrack(current_time, current_location, visited_indices, path):
    global best_itinerary, best_length

    if len(path) > best_length:
        best_length = len(path)
        best_itinerary = deepcopy(path)

    for i in range(len(friends)):
        if i in visited_indices:
            continue
        friend = friends[i]
        location = friend['location']
        if current_location not in travel_times or location not in travel_times[current_location]:
            continue
        travel_time = travel_times[current_location][location]
        arrival_time = current_time + travel_time

        latest_start = friend['available_end'] - friend['min_duration']
        if arrival_time > friend['available_end']:
            continue
        start_time = max(arrival_time, friend['available_start'])
        end_time = start_time + friend['min_duration']
        if end_time > friend['available_end']:
            continue

        visited_indices.add(i)
        path.append({
            'action': 'meet',
            'location': location,
            'person': friend['name'],
            'start_time': minutes_to_time(start_time),
            'end_time': minutes_to_time(end_time)
        })
        backtrack(end_time, location, visited_indices, path)
        visited_indices.remove(i)
        path.pop()

initial_time = to_minutes('9:00AM')
initial_location = 'Embarcadero'

backtrack(initial_time, initial_location, set(), [])

result = {
    "itinerary": best_itinerary
}
print(json.dumps(result, indent=2))