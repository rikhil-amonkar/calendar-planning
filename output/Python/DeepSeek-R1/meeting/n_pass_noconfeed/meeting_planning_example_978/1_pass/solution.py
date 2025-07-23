import json

def time_to_minutes(s):
    if s.endswith('AM') or s.endswith('PM'):
        time_part = s[:-2].strip()
        if ':' in time_part:
            hour, minute = time_part.split(':')
        else:
            hour = time_part
            minute = '0'
        hour = int(hour)
        minute = int(minute)
        if 'PM' in s and hour != 12:
            hour += 12
        if 'AM' in s and hour == 12:
            hour = 0
        return hour * 60 + minute
    else:
        hour, minute = s.split(':')
        return int(hour) * 60 + int(minute)

def minutes_to_time(m):
    hour = m // 60
    minute = m % 60
    return f"{hour}:{minute:02d}"

travel_times = {
    "Embarcadero": {
        "Fisherman's Wharf": 6,
        "Financial District": 5,
        "Russian Hill": 8,
        "Marina District": 12,
        "Richmond District": 21,
        "Pacific Heights": 11,
        "Haight-Ashbury": 21,
        "Presidio": 20,
        "Nob Hill": 10,
        "The Castro": 25
    },
    "Fisherman's Wharf": {
        "Embarcadero": 8,
        "Financial District": 11,
        "Russian Hill": 7,
        "Marina District": 9,
        "Richmond District": 18,
        "Pacific Heights": 12,
        "Haight-Ashbury": 22,
        "Presidio": 17,
        "Nob Hill": 11,
        "The Castro": 27
    },
    "Financial District": {
        "Embarcadero": 4,
        "Fisherman's Wharf": 10,
        "Russian Hill": 11,
        "Marina District": 15,
        "Richmond District": 21,
        "Pacific Heights": 13,
        "Haight-Ashbury": 19,
        "Presidio": 22,
        "Nob Hill": 8,
        "The Castro": 20
    },
    "Russian Hill": {
        "Embarcadero": 8,
        "Fisherman's Wharf": 7,
        "Financial District": 11,
        "Marina District": 7,
        "Richmond District": 14,
        "Pacific Heights": 7,
        "Haight-Ashbury": 17,
        "Presidio": 14,
        "Nob Hill": 5,
        "The Castro": 21
    },
    "Marina District": {
        "Embarcadero": 14,
        "Fisherman's Wharf": 10,
        "Financial District": 17,
        "Russian Hill": 8,
        "Richmond District": 11,
        "Pacific Heights": 7,
        "Haight-Ashbury": 16,
        "Presidio": 10,
        "Nob Hill": 12,
        "The Castro": 22
    },
    "Richmond District": {
        "Embarcadero": 19,
        "Fisherman's Wharf": 18,
        "Financial District": 22,
        "Russian Hill": 13,
        "Marina District": 9,
        "Pacific Heights": 10,
        "Haight-Ashbury": 10,
        "Presidio": 7,
        "Nob Hill": 17,
        "The Castro": 16
    },
    "Pacific Heights": {
        "Embarcadero": 10,
        "Fisherman's Wharf": 13,
        "Financial District": 13,
        "Russian Hill": 7,
        "Marina District": 6,
        "Richmond District": 12,
        "Haight-Ashbury": 11,
        "Presidio": 11,
        "Nob Hill": 8,
        "The Castro": 16
    },
    "Haight-Ashbury": {
        "Embarcadero": 20,
        "Fisherman's Wharf": 23,
        "Financial District": 21,
        "Russian Hill": 17,
        "Marina District": 17,
        "Richmond District": 10,
        "Pacific Heights": 12,
        "Presidio": 15,
        "Nob Hill": 15,
        "The Castro": 6
    },
    "Presidio": {
        "Embarcadero": 20,
        "Fisherman's Wharf": 19,
        "Financial District": 23,
        "Russian Hill": 14,
        "Marina District": 11,
        "Richmond District": 7,
        "Pacific Heights": 11,
        "Haight-Ashbury": 15,
        "Nob Hill": 18,
        "The Castro": 21
    },
    "Nob Hill": {
        "Embarcadero": 9,
        "Fisherman's Wharf": 10,
        "Financial District": 9,
        "Russian Hill": 5,
        "Marina District": 11,
        "Richmond District": 14,
        "Pacific Heights": 8,
        "Haight-Ashbury": 13,
        "Presidio": 17,
        "The Castro": 17
    },
    "The Castro": {
        "Embarcadero": 22,
        "Fisherman's Wharf": 24,
        "Financial District": 21,
        "Russian Hill": 18,
        "Marina District": 21,
        "Richmond District": 16,
        "Pacific Heights": 16,
        "Haight-Ashbury": 6,
        "Presidio": 20,
        "Nob Hill": 16
    }
}

friends = [
    {'name': 'Stephanie', 'location': "Fisherman's Wharf", 'start': time_to_minutes("3:30PM"), 'end': time_to_minutes("10:00PM"), 'min_duration': 30},
    {'name': 'Lisa', 'location': "Financial District", 'start': time_to_minutes("10:45AM"), 'end': time_to_minutes("5:15PM"), 'min_duration': 15},
    {'name': 'Melissa', 'location': "Russian Hill", 'start': time_to_minutes("5:00PM"), 'end': time_to_minutes("9:45PM"), 'min_duration': 120},
    {'name': 'Betty', 'location': "Marina District", 'start': time_to_minutes("10:45AM"), 'end': time_to_minutes("2:15PM"), 'min_duration': 60},
    {'name': 'Sarah', 'location': "Richmond District", 'start': time_to_minutes("4:15PM"), 'end': time_to_minutes("7:30PM"), 'min_duration': 105},
    {'name': 'Daniel', 'location': "Pacific Heights", 'start': time_to_minutes("6:30PM"), 'end': time_to_minutes("9:45PM"), 'min_duration': 60},
    {'name': 'Joshua', 'location': "Haight-Ashbury", 'start': time_to_minutes("9:00AM"), 'end': time_to_minutes("3:30PM"), 'min_duration': 15},
    {'name': 'Joseph', 'location': "Presidio", 'start': time_to_minutes("7:00AM"), 'end': time_to_minutes("1:00PM"), 'min_duration': 45},
    {'name': 'Andrew', 'location': "Nob Hill", 'start': time_to_minutes("7:45PM"), 'end': time_to_minutes("10:00PM"), 'min_duration': 105},
    {'name': 'John', 'location': "The Castro", 'start': time_to_minutes("1:15PM"), 'end': time_to_minutes("7:45PM"), 'min_duration': 45}
]

all_locations = set(travel_times.keys())

dp = {}
parent = {}
n = len(friends)
dp[(0, 'Embarcadero')] = 540

for mask in range(1 << n):
    for loc in all_locations:
        state = (mask, loc)
        if state not in dp:
            continue
        current_time = dp[state]
        for i in range(n):
            if mask & (1 << i):
                continue
            f = friends[i]
            if loc not in travel_times or f.location not in travel_times[loc]:
                continue
            travel_time = travel_times[loc][f.location]
            arrival = current_time + travel_time
            start_meeting = max(arrival, f.start)
            end_meeting = start_meeting + f.min_duration
            if end_meeting > f.end:
                continue
            new_mask = mask | (1 << i)
            new_loc = f.location
            new_state = (new_mask, new_loc)
            if new_state not in dp or end_meeting < dp[new_state]:
                dp[new_state] = end_meeting
                parent[new_state] = (mask, loc, f.name, start_meeting, end_meeting, f.location)

best_mask = None
best_loc = None
best_count = -1
for (mask, loc), time in dp.items():
    count = bin(mask).count("1")
    if count > best_count:
        best_count = count
        best_mask = mask
        best_loc = loc

itinerary_rev = []
current_state = (best_mask, best_loc)
while current_state in parent:
    mask, loc, name, start_meeting, end_meeting, location = parent[current_state]
    itinerary_rev.append({
        'action': 'meet',
        'location': location,
        'person': name,
        'start_time': minutes_to_time(start_meeting),
        'end_time': minutes_to_time(end_meeting)
    })
    current_state = (mask, loc)

itinerary = itinerary_rev[::-1]
result = {
    "itinerary": itinerary
}
print(json.dumps(result))