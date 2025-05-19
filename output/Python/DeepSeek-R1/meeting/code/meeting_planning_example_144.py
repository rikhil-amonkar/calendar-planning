import datetime
from datetime import datetime as dt, timedelta
import itertools
import json

def parse_time(time_str):
    return dt.strptime(time_str, '%H:%M')

def time_to_str(dt_obj):
    return f"{dt_obj.hour}:{dt_obj.minute:02d}"

travel_times = {
    ('The Castro', 'Mission District'): 7,
    ('The Castro', 'Financial District'): 20,
    ('Mission District', 'The Castro'): 7,
    ('Mission District', 'Financial District'): 17,
    ('Financial District', 'The Castro'): 23,
    ('Financial District', 'Mission District'): 17,
}

friends = [
    {
        'name': 'Laura',
        'location': 'Mission District',
        'available_start': '12:15',
        'available_end': '19:45',
        'duration': 75,
    },
    {
        'name': 'Anthony',
        'location': 'Financial District',
        'available_start': '12:30',
        'available_end': '14:45',
        'duration': 30,
    }
]

parsed_friends = []
for friend in friends:
    start = parse_time(friend['available_start'])
    end = parse_time(friend['available_end'])
    parsed_friend = {
        'name': friend['name'],
        'location': friend['location'],
        'start': dt(year=2000, month=1, day=1, hour=start.hour, minute=start.minute),
        'end': dt(year=2000, month=1, day=1, hour=end.hour, minute=end.minute),
        'duration': friend['duration']
    }
    parsed_friends.append(parsed_friend)

current_location = 'The Castro'
current_time = dt(year=2000, month=1, day=1, hour=9, minute=0)

best_itinerary = None
best_end_time = None

for permutation in itertools.permutations(parsed_friends):
    temp_time = current_time
    temp_location = current_location
    itinerary = []
    valid = True
    for friend in permutation:
        travel_key = (temp_location, friend['location'])
        if travel_key not in travel_times:
            valid = False
            break
        travel_duration = travel_times[travel_key]
        arrival_time = temp_time + timedelta(minutes=travel_duration)
        if arrival_time > friend['end']:
            valid = False
            break
        start_meeting = max(arrival_time, friend['start'])
        end_meeting = start_meeting + timedelta(minutes=friend['duration'])
        if end_meeting > friend['end']:
            valid = False
            break
        itinerary.append({
            "action": "meet",
            "location": friend['location'],
            "person": friend['name'],
            "start_time": time_to_str(start_meeting),
            "end_time": time_to_str(end_meeting)
        })
        temp_time = end_meeting
        temp_location = friend['location']
    if valid and len(itinerary) == len(parsed_friends):
        if best_itinerary is None or temp_time < best_end_time:
            best_itinerary = itinerary
            best_end_time = temp_time

output = {"itinerary": best_itinerary} if best_itinerary else {"itinerary": []}
print(json.dumps(output, indent=2))