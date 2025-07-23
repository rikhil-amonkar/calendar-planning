import json

def parse_time(s):
    s = s.strip().replace(' ', '')
    if s.endswith('PM') or s.endswith('AM'):
        meridian = s[-2:]
        time_str = s[:-2]
        parts = time_str.split(':')
        hour = int(parts[0])
        minute = int(parts[1])
        if meridian == 'PM':
            if hour != 12:
                hour += 12
        else:
            if hour == 12:
                hour = 0
        total_minutes = hour * 60 + minute
        return total_minutes - 540
    else:
        raise ValueError(f"Unknown meridian in {s}")

def minutes_to_time(minutes):
    total_minutes_since_midnight = minutes + 540
    hour = total_minutes_since_midnight // 60
    minute = total_minutes_since_midnight % 60
    return f"{hour}:{minute:02d}"

# Build travel_times dictionary
travel_times = {
    "Union Square": {
        "The Castro": 17, "North Beach": 10, "Embarcadero": 11, "Alamo Square": 15, 
        "Nob Hill": 9, "Presidio": 24, "Fisherman's Wharf": 15, "Mission District": 14, 
        "Haight-Ashbury": 18
    },
    "The Castro": {
        "Union Square": 19, "North Beach": 20, "Embarcadero": 22, "Alamo Square": 8, 
        "Nob Hill": 16, "Presidio": 20, "Fisherman's Wharf": 24, "Mission District": 7, 
        "Haight-Ashbury": 6
    },
    "North Beach": {
        "Union Square": 7, "The Castro": 23, "Embarcadero": 6, "Alamo Square": 16, 
        "Nob Hill": 7, "Presidio": 17, "Fisherman's Wharf": 5, "Mission District": 18, 
        "Haight-Ashbury": 18
    },
    "Embarcadero": {
        "Union Square": 10, "The Castro": 25, "North Beach": 5, "Alamo Square": 19, 
        "Nob Hill": 10, "Presidio": 20, "Fisherman's Wharf": 6, "Mission District": 20, 
        "Haight-Ashbury": 21
    },
    "Alamo Square": {
        "Union Square": 14, "The Castro": 8, "North Beach": 15, "Embarcadero": 16, 
        "Nob Hill": 11, "Presidio": 17, "Fisherman's Wharf": 19, "Mission District": 10, 
        "Haight-Ashbury": 5
    },
    "Nob Hill": {
        "Union Square": 7, "The Castro": 17, "North Beach": 8, "Embarcadero": 9, 
        "Alamo Square": 11, "Presidio": 17, "Fisherman's Wharf": 10, "Mission District": 13, 
        "Haight-Ashbury": 13
    },
    "Presidio": {
        "Union Square": 22, "The Castro": 21, "North Beach": 18, "Embarcadero": 20, 
        "Alamo Square": 19, "Nob Hill": 18, "Fisherman's Wharf": 19, "Mission District": 26, 
        "Haight-Ashbury": 15
    },
    "Fisherman's Wharf": {
        "Union Square": 13, "The Castro": 27, "North Beach": 6, "Embarcadero": 8, 
        "Alamo Square": 21, "Nob Hill": 11, "Presidio": 17, "Mission District": 22, 
        "Haight-Ashbury": 22
    },
    "Mission District": {
        "Union Square": 15, "The Castro": 7, "North Beach": 17, "Embarcadero": 19, 
        "Alamo Square": 11, "Nob Hill": 12, "Presidio": 25, "Fisherman's Wharf": 22, 
        "Haight-Ashbury": 12
    },
    "Haight-Ashbury": {
        "Union Square": 19, "The Castro": 6, "North Beach": 19, "Embarcadero": 20, 
        "Alamo Square": 5, "Nob Hill": 15, "Presidio": 15, "Fisherman's Wharf": 23, 
        "Mission District": 11
    }
}

# Define events with adjusted window_start
events = [
    {'name': 'Melissa', 'location': 'The Castro', 'window_start': parse_time('8:15PM'), 'window_end': parse_time('9:15PM'), 'min_duration': 30},
    {'name': 'Kimberly', 'location': 'North Beach', 'window_start': parse_time('7:00AM'), 'window_end': parse_time('10:30AM'), 'min_duration': 15},
    {'name': 'Joseph', 'location': 'Embarcadero', 'window_start': parse_time('3:30PM'), 'window_end': parse_time('7:30PM'), 'min_duration': 75},
    {'name': 'Barbara', 'location': 'Alamo Square', 'window_start': parse_time('8:45PM'), 'window_end': parse_time('9:45PM'), 'min_duration': 15},
    {'name': 'Kenneth', 'location': 'Nob Hill', 'window_start': parse_time('12:15PM'), 'window_end': parse_time('5:15PM'), 'min_duration': 105},
    {'name': 'Joshua', 'location': 'Presidio', 'window_start': parse_time('4:30PM'), 'window_end': parse_time('6:15PM'), 'min_duration': 105},
    {'name': 'Brian', 'location': "Fisherman's Wharf", 'window_start': parse_time('9:30AM'), 'window_end': parse_time('3:30PM'), 'min_duration': 45},
    {'name': 'Steven', 'location': 'Mission District', 'window_start': parse_time('7:30PM'), 'window_end': parse_time('9:00PM'), 'min_duration': 90},
    {'name': 'Betty', 'location': 'Haight-Ashbury', 'window_start': parse_time('7:00PM'), 'window_end': parse_time('8:30PM'), 'min_duration': 90}
]

# Adjust window_start to be at least 0
for event in events:
    event['window_start_adj'] = max(0, event['window_start'])

n = len(events)
INF = 10**9
dp = [[INF] * (n+1) for _ in range(1<<n)]
parent_mask = [[-1] * (n+1) for _ in range(1<<n)]
parent_last = [[-2] * (n+1) for _ in range(1<<n)]

# Initialize: mask=0, last=-1 -> index0 in the last dimension
dp[0][0] = 0

# Iterate over masks and last
for mask in range(1<<n):
    for last in range(-1, n):
        idx_last = last+1
        if dp[mask][idx_last] == INF:
            continue
        current_time = dp[mask][idx_last]
        current_location = "Union Square" if last == -1 else events[last]['location']
        for j in range(n):
            if mask & (1<<j):
                continue
            next_location = events[j]['location']
            travel_time = travel_times[current_location][next_location]
            arrival_time = current_time + travel_time
            start_time = max(arrival_time, events[j]['window_start_adj'])
            end_time = start_time + events[j]['min_duration']
            if end_time > events[j]['window_end']:
                continue
            new_mask = mask | (1<<j)
            new_last = j
            idx_new_last = new_last+1
            if end_time < dp[new_mask][idx_new_last]:
                dp[new_mask][idx_new_last] = end_time
                parent_mask[new_mask][idx_new_last] = mask
                parent_last[new_mask][idx_new_last] = last

# Find the state with the maximum count
best_mask = 0
best_last = -1
best_count = -1
for mask in range(1<<n):
    for last in range(-1, n):
        idx_last = last+1
        if dp[mask][idx_last] == INF:
            continue
        count = bin(mask).count("1")
        if count > best_count:
            best_count = count
            best_mask = mask
            best_last = last

# Backtrack to get the itinerary
itinerary = []
current_mask = best_mask
current_last = best_last
while current_mask != 0:
    idx_current_last = current_last+1
    prev_mask = parent_mask[current_mask][idx_current_last]
    prev_last = parent_last[current_mask][idx_current_last]
    j = current_last
    # Compute start_time: end_time - min_duration
    end_time = dp[current_mask][idx_current_last]
    start_time = end_time - events[j]['min_duration']
    # Create meeting entry
    meeting = {
        'action': 'meet',
        'location': events[j]['location'],
        'person': events[j]['name'],
        'start_time': minutes_to_time(start_time),
        'end_time': minutes_to_time(end_time)
    }
    itinerary.append(meeting)
    current_mask = prev_mask
    current_last = prev_last

# Reverse to get chronological order
itinerary.reverse()

# Output as JSON
result = {"itinerary": itinerary}
print(json.dumps(result))