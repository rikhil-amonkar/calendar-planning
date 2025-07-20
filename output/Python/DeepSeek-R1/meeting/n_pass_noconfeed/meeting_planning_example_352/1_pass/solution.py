import itertools
import json

def time_to_minutes(time_str):
    parts = time_str.split(':')
    hours = int(parts[0])
    minutes = int(parts[1])
    return hours * 60 + minutes

def minutes_to_time(minutes_val):
    hours = minutes_val // 60
    minutes = minutes_val % 60
    return f"{hours}:{minutes:02d}"

travel_times = {
    "Union Square": {"Nob Hill": 9, "Haight-Ashbury": 18, "Chinatown": 7, "Marina District": 18},
    "Nob Hill": {"Union Square": 7, "Haight-Ashbury": 13, "Chinatown": 6, "Marina District": 11},
    "Haight-Ashbury": {"Union Square": 17, "Nob Hill": 15, "Chinatown": 19, "Marina District": 17},
    "Chinatown": {"Union Square": 7, "Nob Hill": 8, "Haight-Ashbury": 19, "Marina District": 12},
    "Marina District": {"Union Square": 16, "Nob Hill": 12, "Haight-Ashbury": 16, "Chinatown": 16}
}

friends_data = [
    {"name": "Karen", "location": "Nob Hill", "avail_start": time_to_minutes("21:15"), "avail_end": time_to_minutes("21:45"), "duration": 30},
    {"name": "Joseph", "location": "Haight-Ashbury", "avail_start": time_to_minutes("12:30"), "avail_end": time_to_minutes("19:45"), "duration": 90},
    {"name": "Sandra", "location": "Chinatown", "avail_start": time_to_minutes("7:15"), "avail_end": time_to_minutes("19:15"), "duration": 75},
    {"name": "Nancy", "location": "Marina District", "avail_start": time_to_minutes("11:00"), "avail_end": time_to_minutes("20:15"), "duration": 105}
]

karen = None
non_karen = []
for f in friends_data:
    if f['name'] == 'Karen':
        karen = f
    else:
        non_karen.append(f)

start_location = "Union Square"
start_time = time_to_minutes("9:00")

def simulate(start_loc, start_min, friend_list, travel_dict):
    current_location = start_loc
    current_time = start_min
    itinerary = []
    for friend in friend_list:
        from_loc = current_location
        to_loc = friend['location']
        travel_duration = travel_dict[from_loc][to_loc]
        arrival_time = current_time + travel_duration
        meeting_start = max(arrival_time, friend['avail_start'])
        meeting_end = meeting_start + friend['duration']
        if meeting_end > friend['avail_end']:
            return None
        itinerary.append({
            'action': 'meet',
            'location': to_loc,
            'person': friend['name'],
            'start_time': minutes_to_time(meeting_start),
            'end_time': minutes_to_time(meeting_end)
        })
        current_location = to_loc
        current_time = meeting_end
    return itinerary

best_itinerary = None
found = False

for perm in itertools.permutations(non_karen):
    friend_list_4 = list(perm) + [karen]
    itinerary = simulate(start_location, start_time, friend_list_4, travel_times)
    if itinerary is not None:
        best_itinerary = itinerary
        found = True
        break

if not found:
    for perm in itertools.permutations(non_karen):
        friend_list_3a = list(perm)
        itinerary = simulate(start_location, start_time, friend_list_3a, travel_times)
        if itinerary is not None:
            best_itinerary = itinerary
            found = True
            break

if not found:
    for subset in itertools.combinations(non_karen, 2):
        for perm in itertools.permutations(subset):
            friend_list_3b = list(perm) + [karen]
            itinerary = simulate(start_location, start_time, friend_list_3b, travel_times)
            if itinerary is not None:
                best_itinerary = itinerary
                found = True
                break
        if found:
            break

if not found:
    for subset in itertools.combinations(non_karen, 2):
        for perm in itertools.permutations(subset):
            friend_list_2a = list(perm)
            itinerary = simulate(start_location, start_time, friend_list_2a, travel_times)
            if itinerary is not None:
                best_itinerary = itinerary
                found = True
                break
        if found:
            break

if not found:
    for friend in non_karen:
        friend_list_2b = [friend, karen]
        itinerary = simulate(start_location, start_time, friend_list_2b, travel_times)
        if itinerary is not None:
            best_itinerary = itinerary
            found = True
            break

if not found:
    friend_list_1 = [karen]
    best_itinerary = simulate(start_location, start_time, friend_list_1, travel_times)

output = {"itinerary": best_itinerary}
print(json.dumps(output))