import itertools
import json

def time_to_minutes(time_str):
    h, m = map(int, time_str.split(':'))
    return h * 60 + m

def minutes_to_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m}"

friends = [
    {
        'name': 'Sarah',
        'location': "Fisherman's Wharf",
        'available_start': time_to_minutes("14:45"),
        'available_end': time_to_minutes("17:30"),
        'required_duration': 105,
    },
    {
        'name': 'Mary',
        'location': 'Richmond District',
        'available_start': time_to_minutes("13:00"),
        'available_end': time_to_minutes("19:15"),
        'required_duration': 75,
    },
    {
        'name': 'Helen',
        'location': 'Mission District',
        'available_start': time_to_minutes("21:45"),
        'available_end': time_to_minutes("22:30"),
        'required_duration': 30,
    },
    {
        'name': 'Thomas',
        'location': 'Bayview',
        'available_start': time_to_minutes("15:15"),
        'available_end': time_to_minutes("18:45"),
        'required_duration': 120,
    },
]

travel_times = {
    'Haight-Ashbury': {
        "Fisherman's Wharf": 23,
        'Richmond District': 10,
        'Mission District': 11,
        'Bayview': 18,
    },
    "Fisherman's Wharf": {
        'Haight-Ashbury': 22,
        'Richmond District': 18,
        'Mission District': 22,
        'Bayview': 26,
    },
    'Richmond District': {
        'Haight-Ashbury': 10,
        'Fisherman's Wharf': 18,
        'Mission District': 20,
        'Bayview': 26,
    },
    'Mission District': {
        'Haight-Ashbury': 12,
        'Fisherman's Wharf': 22,
        'Richmond District': 20,
        'Bayview': 15,
    },
    'Bayview': {
        'Haight-Ashbury': 19,
        'Fisherman's Wharf': 25,
        'Richmond District': 25,
        'Mission District': 13,
    },
}

start_location = 'Haight-Ashbury'
start_time = time_to_minutes('9:00')

best_itinerary = None
best_num_friends = 0
best_end_time = float('inf')

for subset_size in range(4, 0, -1):
    for subset in itertools.combinations(friends, subset_size):
        for perm in itertools.permutations(subset):
            current_time = start_time
            current_location = start_location
            itinerary = []
            valid = True
            
            for friend in perm:
                dest_location = friend['location']
                travel_time = travel_times[current_location][dest_location]
                arrival_time = current_time + travel_time
                
                available_start = friend['available_start']
                available_end = friend['available_end']
                required = friend['required_duration']
                
                meeting_start = max(arrival_time, available_start)
                
                if meeting_start + required > available_end:
                    valid = False
                    break
                
                meeting_end = meeting_start + required
                itinerary.append({
                    'action': 'meet',
                    'location': dest_location,
                    'person': friend['name'],
                    'start_time': minutes_to_time(meeting_start),
                    'end_time': minutes_to_time(meeting_end)
                })
                
                current_time = meeting_end
                current_location = dest_location
            
            if valid:
                current_num_friends = len(itinerary)
                current_end_time = current_time
                
                if (current_num_friends > best_num_friends) or \
                   (current_num_friends == best_num_friends and current_end_time < best_end_time):
                    best_itinerary = itinerary
                    best_num_friends = current_num_friends
                    best_end_time = current_end_time

output = {
    "itinerary": best_itinerary if best_itinerary else []
}

print(json.dumps(output, indent=2))