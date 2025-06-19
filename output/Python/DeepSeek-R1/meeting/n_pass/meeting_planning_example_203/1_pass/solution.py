import itertools
import json

def time_to_minutes(time_str):
    parts = time_str.split(':')
    hour = int(parts[0])
    minute = int(parts[1])
    total_minutes = (hour - 9) * 60 + minute
    return total_minutes

def minutes_to_time(minutes):
    total_minutes = minutes
    hour = 9 + total_minutes // 60
    minute = total_minutes % 60
    return f"{hour}:{minute:02d}"

def try_schedule(sequence, travel_times, start_location, start_time):
    current_time = start_time
    current_loc = start_location
    itinerary = []
    for friend in sequence:
        if current_loc == friend['location']:
            travel_time = 0
        else:
            travel_time = travel_times[current_loc][friend['location']]
        current_time += travel_time
        start_meeting = max(current_time, friend['available_start'])
        end_meeting = start_meeting + friend['min_duration']
        if end_meeting > friend['available_end']:
            break
        itinerary.append({
            "action": "meet",
            "location": friend['location'],
            "person": friend['name'],
            "start_time": minutes_to_time(start_meeting),
            "end_time": minutes_to_time(end_meeting)
        })
        current_time = end_meeting
        current_loc = friend['location']
    return itinerary

travel_times = {
    "Financial District": {"Fisherman's Wharf": 10, "Pacific Heights": 13, "Mission District": 17},
    "Fisherman's Wharf": {"Financial District": 11, "Pacific Heights": 12, "Mission District": 22},
    "Pacific Heights": {"Financial District": 13, "Fisherman's Wharf": 13, "Mission District": 15},
    "Mission District": {"Financial District": 17, "Fisherman's Wharf": 22, "Pacific Heights": 16}
}

friends = [
    {"name": "David", "location": "Fisherman's Wharf", "available_start": time_to_minutes("10:45"), "available_end": time_to_minutes("15:30"), "min_duration": 15},
    {"name": "Timothy", "location": "Pacific Heights", "available_start": time_to_minutes("9:00"), "available_end": time_to_minutes("15:30"), "min_duration": 75},
    {"name": "Robert", "location": "Mission District", "available_start": time_to_minutes("12:15"), "available_end": time_to_minutes("19:45"), "min_duration": 90}
]

start_location = "Financial District"
start_time_minutes = 0
output_itinerary = None

for perm in itertools.permutations(friends):
    itinerary = try_schedule(perm, travel_times, start_location, start_time_minutes)
    if len(itinerary) == 3:
        output_itinerary = itinerary
        break

if output_itinerary is None:
    found = False
    for pair in itertools.combinations(friends, 2):
        for perm in itertools.permutations(pair):
            itinerary = try_schedule(perm, travel_times, start_location, start_time_minutes)
            if len(itinerary) == 2:
                output_itinerary = itinerary
                found = True
                break
        if found:
            break

if output_itinerary is None:
    candidates = []
    for friend in friends:
        travel_time = travel_times[start_location][friend['location']]
        arrival = start_time_minutes + travel_time
        start_meeting = max(arrival, friend['available_start'])
        end_meeting = start_meeting + friend['min_duration']
        if end_meeting <= friend['available_end']:
            meeting = {
                "action": "meet",
                "location": friend['location'],
                "person": friend['name'],
                "start_time": minutes_to_time(start_meeting),
                "end_time": minutes_to_time(end_meeting)
            }
            candidates.append((start_meeting, [meeting]))
    if candidates:
        candidates.sort(key=lambda x: x[0])
        output_itinerary = candidates[0][1]
    else:
        output_itinerary = []

result = {"itinerary": output_itinerary}
print(json.dumps(result))