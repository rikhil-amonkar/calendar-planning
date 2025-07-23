import itertools
import json

def minutes_to_time_str(total_minutes):
    hours = total_minutes // 60
    minutes = total_minutes % 60
    return f"{hours}:{minutes:02d}"

travel_times = {
    "Sunset District": {
        "Russian Hill": 24,
        "The Castro": 17,
        "Richmond District": 12,
        "Marina District": 21,
        "North Beach": 29,
        "Union Square": 30,
        "Golden Gate Park": 11
    },
    "Russian Hill": {
        "Sunset District": 23,
        "The Castro": 21,
        "Richmond District": 14,
        "Marina District": 7,
        "North Beach": 5,
        "Union Square": 11,
        "Golden Gate Park": 21
    },
    "The Castro": {
        "Sunset District": 17,
        "Russian Hill": 18,
        "Richmond District": 16,
        "Marina District": 21,
        "North Beach": 20,
        "Union Square": 19,
        "Golden Gate Park": 11
    },
    "Richmond District": {
        "Sunset District": 11,
        "Russian Hill": 13,
        "The Castro": 16,
        "Marina District": 9,
        "North Beach": 17,
        "Union Square": 21,
        "Golden Gate Park": 9
    },
    "Marina District": {
        "Sunset District": 19,
        "Russian Hill": 8,
        "The Castro": 22,
        "Richmond District": 11,
        "North Beach": 11,
        "Union Square": 16,
        "Golden Gate Park": 18
    },
    "North Beach": {
        "Sunset District": 27,
        "Russian Hill": 4,
        "The Castro": 22,
        "Richmond District": 18,
        "Marina District": 9,
        "Union Square": 7,
        "Golden Gate Park": 22
    },
    "Union Square": {
        "Sunset District": 26,
        "Russian Hill": 13,
        "The Castro": 19,
        "Richmond District": 20,
        "Marina District": 18,
        "North Beach": 10,
        "Golden Gate Park": 22
    },
    "Golden Gate Park": {
        "Sunset District": 10,
        "Russian Hill": 19,
        "The Castro": 13,
        "Richmond District": 7,
        "Marina District": 16,
        "North Beach": 24,
        "Union Square": 22
    }
}

friends = [
    {'name': 'Karen', 'location': 'Russian Hill', 'start': 20*60+45, 'end': 21*60+45, 'min_duration': 60},
    {'name': 'Jessica', 'location': 'The Castro', 'start': 15*60+45, 'end': 19*60+30, 'min_duration': 60},
    {'name': 'Matthew', 'location': 'Richmond District', 'start': 7*60+30, 'end': 15*60+15, 'min_duration': 15},
    {'name': 'Michelle', 'location': 'Marina District', 'start': 10*60+30, 'end': 18*60+45, 'min_duration': 75},
    {'name': 'Carol', 'location': 'North Beach', 'start': 12*60, 'end': 17*60, 'min_duration': 90},
    {'name': 'Stephanie', 'location': 'Union Square', 'start': 10*60+45, 'end': 14*60+15, 'min_duration': 30},
    {'name': 'Linda', 'location': 'Golden Gate Park', 'start': 10*60+45, 'end': 22*60, 'min_duration': 90}
]

start_time_minutes = 9 * 60
start_location = "Sunset District"

best_itinerary = []
found = False

for k in range(len(friends), 0, -1):
    if found:
        break
    for subset in itertools.combinations(friends, k):
        if found:
            break
        for perm in itertools.permutations(subset):
            current_time = start_time_minutes
            current_loc = start_location
            feasible = True
            itinerary = []
            for friend in perm:
                from_loc = current_loc
                to_loc = friend['location']
                travel_duration = travel_times[from_loc][to_loc]
                arrival_time = current_time + travel_duration
                meeting_start = max(arrival_time, friend['start'])
                if meeting_start + friend['min_duration'] > friend['end']:
                    feasible = False
                    break
                meeting_end = meeting_start + friend['min_duration']
                itinerary.append({
                    'action': 'meet',
                    'location': to_loc,
                    'person': friend['name'],
                    'start_time': minutes_to_time_str(meeting_start),
                    'end_time': minutes_to_time_str(meeting_end)
                })
                current_time = meeting_end
                current_loc = to_loc
            if feasible:
                best_itinerary = itinerary
                found = True
                break
        if found:
            break

result = {"itinerary": best_itinerary}
print(json.dumps(result))