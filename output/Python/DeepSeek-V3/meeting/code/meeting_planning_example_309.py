import json
from itertools import permutations

def time_to_minutes(time_str):
    if time_str == "9:00AM":
        return 9 * 60
    elif time_str == "9:30AM":
        return 9 * 60 + 30
    elif time_str == "1:30PM":
        return 13 * 60 + 30
    elif time_str == "7:00AM":
        return 7 * 60
    elif time_str == "9:00PM":
        return 21 * 60
    elif time_str == "11:15AM":
        return 11 * 60 + 15
    elif time_str == "1:45PM":
        return 13 * 60 + 45
    elif time_str == "8:30AM":
        return 8 * 60 + 30
    else:
        h, m = map(int, time_str.split(':'))
        return h * 60 + m

def minutes_to_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

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
    ('Fisherman\'s Wharf', 'Bayview'): 26
}

friends = [
    {
        'name': 'Nancy',
        'location': 'Chinatown',
        'available_start': time_to_minutes('9:30AM'),
        'available_end': time_to_minutes('1:30PM'),
        'duration': 90
    },
    {
        'name': 'Mary',
        'location': 'Alamo Square',
        'available_start': time_to_minutes('7:00AM'),
        'available_end': time_to_minutes('9:00PM'),
        'duration': 75
    },
    {
        'name': 'Jessica',
        'location': 'Bayview',
        'available_start': time_to_minutes('11:15AM'),
        'available_end': time_to_minutes('1:45PM'),
        'duration': 45
    },
    {
        'name': 'Rebecca',
        'location': 'Fisherman\'s Wharf',
        'available_start': time_to_minutes('7:00AM'),
        'available_end': time_to_minutes('8:30AM'),
        'duration': 45
    }
]

def calculate_schedule(order):
    current_time = time_to_minutes('9:00AM')
    current_location = 'Financial District'
    schedule = []
    met_friends = set()
    
    for friend_idx in order:
        friend = friends[friend_idx]
        if friend['name'] in met_friends:
            continue
        
        travel_time = travel_times[(current_location, friend['location'])]
        arrival_time = current_time + travel_time
        start_time = max(arrival_time, friend['available_start'])
        end_time = start_time + friend['duration']
        
        if end_time > friend['available_end']:
            continue
        
        schedule.append({
            'action': 'meet',
            'location': friend['location'],
            'person': friend['name'],
            'start_time': minutes_to_time(start_time),
            'end_time': minutes_to_time(end_time)
        })
        
        current_time = end_time
        current_location = friend['location']
        met_friends.add(friend['name'])
    
    return schedule

best_schedule = []
max_meetings = 0

for perm in permutations(range(len(friends))):
    met_friends = set()
    schedule = calculate_schedule(perm)
    if len(schedule) > max_meetings:
        max_meetings = len(schedule)
        best_schedule = schedule
    elif len(schedule) == max_meetings and len(schedule) > 0:
        total_time = sum([time_to_minutes(entry['end_time']) - time_to_minutes(entry['start_time']) for entry in schedule])
        best_total_time = sum([time_to_minutes(entry['end_time']) - time_to_minutes(entry['start_time']) for entry in best_schedule])
        if total_time > best_total_time:
            best_schedule = schedule

result = {
    "itinerary": best_schedule
}

print(json.dumps(result, indent=2))