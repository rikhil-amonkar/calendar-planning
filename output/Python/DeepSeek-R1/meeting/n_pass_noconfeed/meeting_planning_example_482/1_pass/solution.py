import itertools
import json

def time_to_minutes(time_str):
    parts = time_str.split(':')
    hours = int(parts[0])
    minutes = int(parts[1]) if len(parts) > 1 else 0
    return hours * 60 + minutes

def minutes_to_time(minutes_val):
    hours = minutes_val // 60
    minutes = minutes_val % 60
    return f"{hours}:{minutes:02d}"

travel_times = {
    "Haight-Ashbury": {
        "Mission District": 11,
        "Bayview": 18,
        "Pacific Heights": 12,
        "Russian Hill": 17,
        "Fisherman's Wharf": 23
    },
    "Mission District": {
        "Haight-Ashbury": 12,
        "Bayview": 15,
        "Pacific Heights": 16,
        "Russian Hill": 15,
        "Fisherman's Wharf": 22
    },
    "Bayview": {
        "Haight-Ashbury": 19,
        "Mission District": 13,
        "Pacific Heights": 23,
        "Russian Hill": 23,
        "Fisherman's Wharf": 25
    },
    "Pacific Heights": {
        "Haight-Ashbury": 11,
        "Mission District": 15,
        "Bayview": 22,
        "Russian Hill": 7,
        "Fisherman's Wharf": 13
    },
    "Russian Hill": {
        "Haight-Ashbury": 17,
        "Mission District": 16,
        "Bayview": 23,
        "Pacific Heights": 7,
        "Fisherman's Wharf": 7
    },
    "Fisherman's Wharf": {
        "Haight-Ashbury": 22,
        "Mission District": 22,
        "Bayview": 26,
        "Pacific Heights": 12,
        "Russian Hill": 7
    }
}

friends = [
    {
        "name": "Stephanie",
        "location": "Mission District",
        "available_start": "8:15",
        "available_end": "13:45",
        "min_duration": 90
    },
    {
        "name": "Sandra",
        "location": "Bayview",
        "available_start": "13:00",
        "available_end": "19:30",
        "min_duration": 15
    },
    {
        "name": "Richard",
        "location": "Pacific Heights",
        "available_start": "7:15",
        "available_end": "10:15",
        "min_duration": 75
    },
    {
        "name": "Brian",
        "location": "Russian Hill",
        "available_start": "12:15",
        "available_end": "16:00",
        "min_duration": 120
    },
    {
        "name": "Jason",
        "location": "Fisherman's Wharf",
        "available_start": "8:30",
        "available_end": "17:45",
        "min_duration": 60
    }
]

for friend in friends:
    friend['available_start_min'] = time_to_minutes(friend['available_start'])
    friend['available_end_min'] = time_to_minutes(friend['available_end'])

start_location = "Haight-Ashbury"
start_time_min = time_to_minutes("9:00")

max_meetings = 0
best_schedule = None

for perm in itertools.permutations(friends):
    current_loc = start_location
    current_time = start_time_min
    schedule = []
    for friend in perm:
        travel_duration = travel_times[current_loc][friend['location']]
        current_time += travel_duration
        start_meeting = max(current_time, friend['available_start_min'])
        if start_meeting + friend['min_duration'] <= friend['available_end_min']:
            end_meeting = start_meeting + friend['min_duration']
            schedule.append({
                'friend': friend,
                'start': start_meeting,
                'end': end_meeting
            })
            current_time = end_meeting
            current_loc = friend['location']
        else:
            current_loc = friend['location']
    if len(schedule) > max_meetings:
        max_meetings = len(schedule)
        best_schedule = schedule

itinerary = []
if best_schedule is not None:
    for meeting in best_schedule:
        friend = meeting['friend']
        itinerary.append({
            "action": "meet",
            "location": friend['location'],
            "person": friend['name'],
            "start_time": minutes_to_time(meeting['start']),
            "end_time": minutes_to_time(meeting['end'])
        })

result = {"itinerary": itinerary}
print(json.dumps(result))