import itertools
import json

def minutes_to_time_str(m):
    hours = m // 60
    minutes = m % 60
    return f"{hours}:{minutes:02d}"

# Define friends
friends = [
    {
        'name': 'Emily',
        'location': 'Alamo Square',
        'available_start': 11 * 60 + 45,  # 705
        'available_end': 15 * 60 + 15,    # 915
        'required_duration': 105
    },
    {
        'name': 'Barbara',
        'location': 'Union Square',
        'available_start': 16 * 60 + 45,  # 1005
        'available_end': 18 * 60 + 15,    # 1095
        'required_duration': 60
    },
    {
        'name': 'William',
        'location': 'Chinatown',
        'available_start': 17 * 60 + 15,  # 1035
        'available_end': 19 * 60 + 0,     # 1140
        'required_duration': 105
    }
]

travel_times = {
    ('The Castro', 'Alamo Square'): 8,
    ('The Castro', 'Union Square'): 19,
    ('The Castro', 'Chinatown'): 20,
    ('Alamo Square', 'The Castro'): 8,
    ('Alamo Square', 'Union Square'): 14,
    ('Alamo Square', 'Chinatown'): 16,
    ('Union Square', 'The Castro'): 19,
    ('Union Square', 'Alamo Square'): 15,
    ('Union Square', 'Chinatown'): 7,
    ('Chinatown', 'The Castro'): 22,
    ('Chinatown', 'Alamo Square'): 17,
    ('Chinatown', 'Union Square'): 7,
}

best_sequences = []
max_friends = 0

for r in range(1, 4):  # lengths 1, 2, 3
    for perm in itertools.permutations(friends, r):
        current_time = 9 * 60  # 540, 9:00 AM
        current_location = 'The Castro'
        feasible = True
        itinerary = []
        for friend in perm:
            # Travel to friend's location
            src = current_location
            dst = friend['location']
            travel_time = travel_times.get((src, dst), None)
            if travel_time is None:
                feasible = False
                break
            current_time += travel_time
            # Determine start time of meeting
            available_start = friend['available_start']
            available_end = friend['available_end']
            start = max(current_time, available_start)
            # Check if meeting is possible
            if start + friend['required_duration'] > available_end:
                feasible = False
                break
            # Record meeting
            end = start + friend['required_duration']
            itinerary.append((friend, start, end))
            # Update current time and location
            current_time = end
            current_location = dst
        if feasible:
            if len(perm) > max_friends:
                max_friends = len(perm)
                best_sequences = [(perm, itinerary)]
            elif len(perm) == max_friends:
                best_sequences.append((perm, itinerary))

# Choose the first best sequence
if best_sequences:
    best_perm, best_itinerary = best_sequences[0]
else:
    best_itinerary = []

# Generate JSON output
itinerary_json = []
for entry in best_itinerary:
    friend, start, end = entry
    itinerary_json.append({
        "action": "meet",
        "location": friend['location'],
        "person": friend['name'],
        "start_time": minutes_to_time_str(start),
        "end_time": minutes_to_time_str(end)
    })

result = {
    "itinerary": itinerary_json
}

print(json.dumps(result, indent=2))