# SOLUTION:
import itertools
import json

def time_to_minutes(time_str):
    if time_str[-2:] in ['AM', 'PM']:
        suffix = time_str[-2:]
        time_part = time_str[:-2]
    else:
        suffix = ""
        time_part = time_str
    parts = time_part.split(':')
    if len(parts) < 2:
        hour = int(parts[0])
        minute = 0
    else:
        hour = int(parts[0])
        minute = int(parts[1])
    if suffix == "PM" and hour != 12:
        hour += 12
    elif suffix == "AM" and hour == 12:
        hour = 0
    return hour * 60 + minute

def minutes_to_time(mins):
    hours = mins // 60
    minutes = mins % 60
    return f"{hours}:{minutes:02d}"

travel_times = {
    "Marina District": {
        "Mission District": 20,
        "Fisherman's Wharf": 10,
        "Presidio": 10,
        "Union Square": 16,
        "Sunset District": 19,
        "Financial District": 17,
        "Haight-Ashbury": 16,
        "Russian Hill": 8
    },
    "Mission District": {
        "Marina District": 19,
        "Fisherman's Wharf": 22,
        "Presidio": 25,
        "Union Square": 15,
        "Sunset District": 24,
        "Financial District": 15,
        "Haight-Ashbury": 12,
        "Russian Hill": 15
    },
    "Fisherman's Wharf": {
        "Marina District": 9,
        "Mission District": 22,
        "Presidio": 17,
        "Union Square": 13,
        "Sunset District": 27,
        "Financial District": 11,
        "Haight-Ashbury": 22,
        "Russian Hill": 7
    },
    "Presidio": {
        "Marina District": 11,
        "Mission District": 26,
        "Fisherman's Wharf": 19,
        "Union Square": 22,
        "Sunset District": 15,
        "Financial District": 23,
        "Haight-Ashbury": 15,
        "Russian Hill": 14
    },
    "Union Square": {
        "Marina District": 18,
        "Mission District": 14,
        "Fisherman's Wharf": 15,
        "Presidio": 24,
        "Sunset District": 27,
        "Financial District": 9,
        "Haight-Ashbury": 18,
        "Russian Hill": 13
    },
    "Sunset District": {
        "Marina District": 21,
        "Mission District": 25,
        "Fisherman's Wharf": 29,
        "Presidio": 16,
        "Union Square": 30,
        "Financial District": 30,
        "Haight-Ashbury": 15,
        "Russian Hill": 24
    },
    "Financial District": {
        "Marina District": 15,
        "Mission District": 17,
        "Fisherman's Wharf": 10,
        "Presidio": 22,
        "Union Square": 9,
        "Sunset District": 30,
        "Haight-Ashbury": 19,
        "Russian Hill": 11
    },
    "Haight-Ashbury": {
        "Marina District": 17,
        "Mission District": 11,
        "Fisherman's Wharf": 23,
        "Presidio": 15,
        "Union Square": 19,
        "Sunset District": 15,
        "Financial District": 21,
        "Russian Hill": 17
    },
    "Russian Hill": {
        "Marina District": 7,
        "Mission District": 16,
        "Fisherman's Wharf": 7,
        "Presidio": 14,
        "Union Square": 10,
        "Sunset District": 23,
        "Financial District": 11,
        "Haight-Ashbury": 17
    }
}

friends = [
    {"name": "Karen", "location": "Mission District", "start_str": "2:15PM", "end_str": "10:00PM", "min_duration": 30},
    {"name": "Richard", "location": "Fisherman's Wharf", "start_str": "2:30PM", "end_str": "5:30PM", "min_duration": 30},
    {"name": "Robert", "location": "Presidio", "start_str": "9:45PM", "end_str": "10:45PM", "min_duration": 60},
    {"name": "Joseph", "location": "Union Square", "start_str": "11:45AM", "end_str": "2:45PM", "min_duration": 120},
    {"name": "Helen", "location": "Sunset District", "start_str": "2:45PM", "end_str": "8:45PM", "min_duration": 105},
    {"name": "Elizabeth", "location": "Financial District", "start_str": "10:00AM", "end_str": "12:45PM", "min_duration": 75},
    {"name": "Kimberly", "location": "Haight-Ashbury", "start_str": "2:15PM", "end_str": "5:30PM", "min_duration": 105},
    {"name": "Ashley", "location": "Russian Hill", "start_str": "11:30AM", "end_str": "9:30PM", "min_duration": 45}
]

for friend in friends:
    friend['start_minutes'] = time_to_minutes(friend['start_str'])
    friend['end_minutes'] = time_to_minutes(friend['end_str'])

best_schedule = None
max_k = -1
start_minutes = 540
start_location = "Marina District"

for k in range(len(friends), 0, -1):
    for subset in itertools.combinations(friends, k):
        for perm in itertools.permutations(subset):
            current_time = start_minutes
            current_location = start_location
            schedule = []
            valid = True
            for friend in perm:
                if current_location == friend['location']:
                    travel_time = 0
                else:
                    travel_time = travel_times[current_location][friend['location']]
                arrival = current_time + travel_time
                start_meeting = max(arrival, friend['start_minutes'])
                end_meeting = start_meeting + friend['min_duration']
                if end_meeting > friend['end_minutes']:
                    valid = False
                    break
                schedule.append({
                    'friend': friend,
                    'start_meeting': start_meeting,
                    'end_meeting': end_meeting
                })
                current_time = end_meeting
                current_location = friend['location']
            if valid:
                best_schedule = schedule
                max_k = k
                break
        if best_schedule is not None:
            break
    if best_schedule is not None:
        break

itinerary = []
if best_schedule is not None:
    for meeting in best_schedule:
        friend = meeting['friend']
        start_time = meeting['start_meeting']
        end_time = meeting['end_meeting']
        itinerary.append({
            "action": "meet",
            "location": friend['location'],
            "person": friend['name'],
            "start_time": minutes_to_time(start_time),
            "end_time": minutes_to_time(end_time)
        })

result = {"itinerary": itinerary}
print(json.dumps(result))