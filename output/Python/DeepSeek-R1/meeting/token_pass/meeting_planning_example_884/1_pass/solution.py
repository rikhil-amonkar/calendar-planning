import itertools
import json

def time_str_to_minutes(time_str):
    time_str = time_str.replace(' ', '')
    if time_str.endswith('AM'):
        time_str = time_str[:-2]
        if ':' in time_str:
            hours, minutes = time_str.split(':')
        else:
            hours = time_str
            minutes = 0
        hours = int(hours)
        if hours == 12:
            hours = 0
        return hours * 60 + int(minutes)
    else:
        time_str = time_str[:-2]
        if ':' in time_str:
            hours, minutes = time_str.split(':')
        else:
            hours = time_str
            minutes = 0
        hours = int(hours)
        if hours != 12:
            hours += 12
        return hours * 60 + int(minutes)

def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02}"

travel_times = {
    'Richmond District': {
        'Richmond District': 0,
        'Chinatown': 20,
        'Sunset District': 11,
        'Alamo Square': 13,
        'Financial District': 22,
        'North Beach': 17,
        'Embarcadero': 19,
        'Presidio': 7,
        'Golden Gate Park': 9,
        'Bayview': 27
    },
    'Chinatown': {
        'Richmond District': 20,
        'Chinatown': 0,
        'Sunset District': 29,
        'Alamo Square': 17,
        'Financial District': 5,
        'North Beach': 3,
        'Embarcadero': 5,
        'Presidio': 19,
        'Golden Gate Park': 23,
        'Bayview': 20
    },
    'Sunset District': {
        'Richmond District': 12,
        'Chinatown': 30,
        'Sunset District': 0,
        'Alamo Square': 17,
        'Financial District': 30,
        'North Beach': 28,
        'Embarcadero': 30,
        'Presidio': 16,
        'Golden Gate Park': 11,
        'Bayview': 22
    },
    'Alamo Square': {
        'Richmond District': 11,
        'Chinatown': 15,
        'Sunset District': 16,
        'Alamo Square': 0,
        'Financial District': 17,
        'North Beach': 15,
        'Embarcadero': 16,
        'Presidio': 17,
        'Golden Gate Park': 9,
        'Bayview': 16
    },
    'Financial District': {
        'Richmond District': 21,
        'Chinatown': 5,
        'Sunset District': 30,
        'Alamo Square': 17,
        'Financial District': 0,
        'North Beach': 7,
        'Embarcadero': 4,
        'Presidio': 22,
        'Golden Gate Park': 23,
        'Bayview': 19
    },
    'North Beach': {
        'Richmond District': 18,
        'Chinatown': 6,
        'Sunset District': 27,
        'Alamo Square': 16,
        'Financial District': 8,
        'North Beach': 0,
        'Embarcadero': 6,
        'Presidio': 17,
        'Golden Gate Park': 22,
        'Bayview': 25
    },
    'Embarcadero': {
        'Richmond District': 21,
        'Chinatown': 7,
        'Sunset District': 30,
        'Alamo Square': 19,
        'Financial District': 5,
        'North Beach': 5,
        'Embarcadero': 0,
        'Presidio': 20,
        'Golden Gate Park': 25,
        'Bayview': 21
    },
    'Presidio': {
        'Richmond District': 7,
        'Chinatown': 21,
        'Sunset District': 15,
        'Alamo Square': 19,
        'Financial District': 23,
        'North Beach': 18,
        'Embarcadero': 20,
        'Presidio': 0,
        'Golden Gate Park': 12,
        'Bayview': 31
    },
    'Golden Gate Park': {
        'Richmond District': 7,
        'Chinatown': 23,
        'Sunset District': 10,
        'Alamo Square': 9,
        'Financial District': 26,
        'North Beach': 23,
        'Embarcadero': 25,
        'Presidio': 11,
        'Golden Gate Park': 0,
        'Bayview': 23
    },
    'Bayview': {
        'Richmond District': 25,
        'Chinatown': 19,
        'Sunset District': 23,
        'Alamo Square': 16,
        'Financial District': 19,
        'North Beach': 22,
        'Embarcadero': 19,
        'Presidio': 32,
        'Golden Gate Park': 22,
        'Bayview': 0
    }
}

friends_data = [
    {
        'name': 'Robert',
        'location': 'Chinatown',
        'start_available': time_str_to_minutes('7:45AM'),
        'end_available': time_str_to_minutes('5:30PM'),
        'min_duration': 120
    },
    {
        'name': 'David',
        'location': 'Sunset District',
        'start_available': time_str_to_minutes('12:30PM'),
        'end_available': time_str_to_minutes('7:45PM'),
        'min_duration': 45
    },
    {
        'name': 'Matthew',
        'location': 'Alamo Square',
        'start_available': time_str_to_minutes('8:45AM'),
        'end_available': time_str_to_minutes('1:45PM'),
        'min_duration': 90
    },
    {
        'name': 'Jessica',
        'location': 'Financial District',
        'start_available': time_str_to_minutes('9:30AM'),
        'end_available': time_str_to_minutes('6:45PM'),
        'min_duration': 45
    },
    {
        'name': 'Melissa',
        'location': 'North Beach',
        'start_available': time_str_to_minutes('7:15AM'),
        'end_available': time_str_to_minutes('4:45PM'),
        'min_duration': 45
    },
    {
        'name': 'Mark',
        'location': 'Embarcadero',
        'start_available': time_str_to_minutes('3:15PM'),
        'end_available': time_str_to_minutes('5:00PM'),
        'min_duration': 45
    },
    {
        'name': 'Deborah',
        'location': 'Presidio',
        'start_available': time_str_to_minutes('7:00PM'),
        'end_available': time_str_to_minutes('7:45PM'),
        'min_duration': 45
    },
    {
        'name': 'Karen',
        'location': 'Golden Gate Park',
        'start_available': time_str_to_minutes('7:30PM'),
        'end_available': time_str_to_minutes('10:00PM'),
        'min_duration': 120
    },
    {
        'name': 'Laura',
        'location': 'Bayview',
        'start_available': time_str_to_minutes('9:15PM'),
        'end_available': time_str_to_minutes('10:15PM'),
        'min_duration': 15
    }
]

class Friend:
    def __init__(self, name, location, start_available, end_available, min_duration):
        self.name = name
        self.location = location
        self.start_available = start_available
        self.end_available = end_available
        self.min_duration = min_duration

friends = []
for data in friends_data:
    friends.append(Friend(data['name'], data['location'], data['start_available'], data['end_available'], data['min_duration']))

start_time = time_str_to_minutes('9:00AM')
start_location = 'Richmond District'

best_count = 0
best_itinerary = []

for perm in itertools.permutations(friends):
    current_time = start_time
    current_location = start_location
    itinerary = []
    for friend in perm:
        travel_duration = travel_times[current_location][friend.location]
        arrival_time = current_time + travel_duration
        if arrival_time > friend.end_available:
            continue
        start_meeting = max(arrival_time, friend.start_available)
        if start_meeting + friend.min_duration > friend.end_available:
            continue
        end_meeting = start_meeting + friend.min_duration
        itinerary.append({
            'action': 'meet',
            'location': friend.location,
            'person': friend.name,
            'start_time': minutes_to_time(start_meeting),
            'end_time': minutes_to_time(end_meeting)
        })
        current_time = end_meeting
        current_location = friend.location
    if len(itinerary) > best_count:
        best_count = len(itinerary)
        best_itinerary = itinerary

output = {
    "itinerary": best_itinerary
}

print(json.dumps(output, indent=2))