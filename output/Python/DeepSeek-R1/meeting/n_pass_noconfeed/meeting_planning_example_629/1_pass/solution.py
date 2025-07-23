import itertools
import json

def time_str_to_minutes(timestr):
    if timestr.endswith('AM') or timestr.endswith('PM'):
        period = timestr[-2:]
        time_part = timestr[:-2].strip()
    else:
        period = ''
        time_part = timestr
    hour, minute = time_part.split(':')
    hour = int(hour)
    minute = int(minute)
    if period == 'PM' and hour != 12:
        hour += 12
    elif period == 'AM' and hour == 12:
        hour = 0
    total_minutes = hour * 60 + minute
    return total_minutes - 540

def minutes_to_time(mins_since_9am):
    total_minutes_from_midnight = mins_since_9am + 540
    hours = total_minutes_from_midnight // 60
    minutes = total_minutes_from_midnight % 60
    return f"{hours}:{minutes:02d}"

travel_times = {
    'Russian Hill': {
        'Presidio': 14, 'Chinatown': 9, 'Pacific Heights': 7, 'Richmond District': 14,
        'Fisherman\'s Wharf': 7, 'Golden Gate Park': 21, 'Bayview': 23
    },
    'Presidio': {
        'Russian Hill': 14, 'Chinatown': 21, 'Pacific Heights': 11, 'Richmond District': 7,
        'Fisherman\'s Wharf': 19, 'Golden Gate Park': 12, 'Bayview': 31
    },
    'Chinatown': {
        'Russian Hill': 7, 'Presidio': 19, 'Pacific Heights': 10, 'Richmond District': 20,
        'Fisherman\'s Wharf': 8, 'Golden Gate Park': 23, 'Bayview': 22
    },
    'Pacific Heights': {
        'Russian Hill': 7, 'Presidio': 11, 'Chinatown': 11, 'Richmond District': 12,
        'Fisherman\'s Wharf': 13, 'Golden Gate Park': 15, 'Bayview': 22
    },
    'Richmond District': {
        'Russian Hill': 13, 'Presidio': 7, 'Chinatown': 20, 'Pacific Heights': 10,
        'Fisherman\'s Wharf': 18, 'Golden Gate Park': 9, 'Bayview': 26
    },
    'Fisherman\'s Wharf': {
        'Russian Hill': 7, 'Presidio': 17, 'Chinatown': 12, 'Pacific Heights': 12,
        'Richmond District': 18, 'Golden Gate Park': 25, 'Bayview': 26
    },
    'Golden Gate Park': {
        'Russian Hill': 19, 'Presidio': 11, 'Chinatown': 23, 'Pacific Heights': 16,
        'Richmond District': 7, 'Fisherman\'s Wharf': 24, 'Bayview': 23
    },
    'Bayview': {
        'Russian Hill': 23, 'Presidio': 31, 'Chinatown': 18, 'Pacific Heights': 23,
        'Richmond District': 25, 'Fisherman\'s Wharf': 25, 'Golden Gate Park': 22
    }
}

friends = [
    {'name': 'Matthew', 'location': 'Presidio', 'start_minutes': time_str_to_minutes('11:00AM'), 
     'end_minutes': time_str_to_minutes('9:00PM'), 'min_duration_minutes': 90},
    {'name': 'Margaret', 'location': 'Chinatown', 'start_minutes': time_str_to_minutes('9:15AM'), 
     'end_minutes': time_str_to_minutes('6:45PM'), 'min_duration_minutes': 90},
    {'name': 'Nancy', 'location': 'Pacific Heights', 'start_minutes': time_str_to_minutes('2:15PM'), 
     'end_minutes': time_str_to_minutes('5:00PM'), 'min_duration_minutes': 15},
    {'name': 'Helen', 'location': 'Richmond District', 'start_minutes': time_str_to_minutes('7:45PM'), 
     'end_minutes': time_str_to_minutes('10:00PM'), 'min_duration_minutes': 60},
    {'name': 'Rebecca', 'location': 'Fisherman\'s Wharf', 'start_minutes': time_str_to_minutes('9:15PM'), 
     'end_minutes': time_str_to_minutes('10:15PM'), 'min_duration_minutes': 60},
    {'name': 'Kimberly', 'location': 'Golden Gate Park', 'start_minutes': time_str_to_minutes('1:00PM'), 
     'end_minutes': time_str_to_minutes('4:30PM'), 'min_duration_minutes': 120},
    {'name': 'Kenneth', 'location': 'Bayview', 'start_minutes': time_str_to_minutes('2:30PM'), 
     'end_minutes': time_str_to_minutes('6:00PM'), 'min_duration_minutes': 60}
]

def simulate_schedule(perm, travel_times):
    current_time = 0
    current_location = 'Russian Hill'
    itinerary = []
    for friend in perm:
        travel = travel_times[current_location][friend['location']]
        arrival = current_time + travel
        start_meeting = max(arrival, friend['start_minutes'])
        end_meeting = start_meeting + friend['min_duration_minutes']
        if end_meeting > friend['end_minutes']:
            return None
        itinerary.append({
            'action': 'meet',
            'location': friend['location'],
            'person': friend['name'],
            'start_time': minutes_to_time(start_meeting),
            'end_time': minutes_to_time(end_meeting)
        })
        current_time = end_meeting
        current_location = friend['location']
    return itinerary

n = len(friends)
best_itinerary = []
found = False
for k in range(n, 0, -1):
    for perm in itertools.permutations(friends, k):
        itinerary = simulate_schedule(perm, travel_times)
        if itinerary is not None:
            best_itinerary = itinerary
            found = True
            break
    if found:
        break

result = {"itinerary": best_itinerary}
print(json.dumps(result))