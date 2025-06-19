import itertools
import json

def parse_time(s):
    if s[-2:] in ['AM', 'PM']:
        period = s[-2:]
        time_str = s[:-2]
    else:
        period = ''
        time_str = s
    parts = time_str.split(':')
    hour = int(parts[0])
    minute = int(parts[1])
    if period == 'PM' and hour != 12:
        hour += 12
    if period == 'AM' and hour == 12:
        hour = 0
    return hour * 60 + minute

def format_time(minutes):
    hour = minutes // 60
    minute = minutes % 60
    return f"{hour}:{minute:02d}"

travel_times = {
    "Embarcadero": {
        "Golden Gate Park": 25,
        "Haight-Ashbury": 21,
        "Bayview": 21,
        "Presidio": 20,
        "Financial District": 5
    },
    "Golden Gate Park": {
        "Embarcadero": 25,
        "Haight-Ashbury": 7,
        "Bayview": 23,
        "Presidio": 11,
        "Financial District": 26
    },
    "Haight-Ashbury": {
        "Embarcadero": 20,
        "Golden Gate Park": 7,
        "Bayview": 18,
        "Presidio": 15,
        "Financial District": 21
    },
    "Bayview": {
        "Embarcadero": 19,
        "Golden Gate Park": 22,
        "Haight-Ashbury": 19,
        "Presidio": 31,
        "Financial District": 19
    },
    "Presidio": {
        "Embarcadero": 20,
        "Golden Gate Park": 12,
        "Haight-Ashbury": 15,
        "Bayview": 31,
        "Financial District": 23
    },
    "Financial District": {
        "Embarcadero": 4,
        "Golden Gate Park": 23,
        "Haight-Ashbury": 19,
        "Bayview": 19,
        "Presidio": 22
    }
}

friends = [
    {"name": "Mary", "location": "Golden Gate Park", "start_str": "8:45AM", "end_str": "11:45AM", "min_duration": 45},
    {"name": "Kevin", "location": "Haight-Ashbury", "start_str": "10:15AM", "end_str": "4:15PM", "min_duration": 90},
    {"name": "Deborah", "location": "Bayview", "start_str": "3:00PM", "end_str": "7:15PM", "min_duration": 120},
    {"name": "Stephanie", "location": "Presidio", "start_str": "10:00AM", "end_str": "5:15PM", "min_duration": 120},
    {"name": "Emily", "location": "Financial District", "start_str": "11:30AM", "end_str": "9:45PM", "min_duration": 105}
]

for friend in friends:
    friend['start_min'] = parse_time(friend['start_str'])
    friend['end_min'] = parse_time(friend['end_str'])
    friend['duration_min'] = friend['min_duration']

best_count = 0
best_itinerary = None
perms = itertools.permutations(friends)
for perm in perms:
    current_time = 540
    current_location = "Embarcadero"
    itinerary_perm = []
    for friend in perm:
        travel_time = travel_times[current_location][friend['location']]
        arrival = current_time + travel_time
        start_meeting = max(arrival, friend['start_min'])
        end_meeting = start_meeting + friend['duration_min']
        if end_meeting <= friend['end_min']:
            itinerary_perm.append({
                'friend': friend['name'],
                'location': friend['location'],
                'start_min': start_meeting,
                'end_min': end_meeting
            })
            current_time = end_meeting
            current_location = friend['location']
    count = len(itinerary_perm)
    if count == 5:
        best_itinerary = itinerary_perm
        best_count = count
        break
    if count > best_count:
        best_count = count
        best_itinerary = itinerary_perm

itinerary_output = []
for meeting in best_itinerary:
    itinerary_output.append({
        "action": "meet",
        "location": meeting['location'],
        "person": meeting['friend'],
        "start_time": format_time(meeting['start_min']),
        "end_time": format_time(meeting['end_min'])
    })

result = {"itinerary": itinerary_output}
print(json.dumps(result))