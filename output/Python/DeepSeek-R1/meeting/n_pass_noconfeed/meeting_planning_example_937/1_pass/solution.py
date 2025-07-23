import json

def time_to_minutes(time_str):
    time_str = time_str.strip()
    period = time_str[-2:]
    time_part = time_str[:-2].strip()
    parts = time_part.split(':')
    hour = int(parts[0])
    minute = int(parts[1])
    if period == "PM" and hour != 12:
        hour += 12
    if period == "AM" and hour == 12:
        hour = 0
    return hour * 60 + minute

def minutes_to_time(minutes):
    hour = minutes // 60
    minute = minutes % 60
    return f"{hour}:{minute:02d}"

# Hardcoded travel times dictionary
travel_times = {
    "Russian Hill": {
        "Sunset District": 23,
        "Union Square": 10,
        "Nob Hill": 5,
        "Marina District": 7,
        "Richmond District": 14,
        "Financial District": 11,
        "Embarcadero": 8,
        "The Castro": 21,
        "Alamo Square": 15,
        "Presidio": 14
    },
    "Sunset District": {
        "Russian Hill": 24,
        "Union Square": 30,
        "Nob Hill": 27,
        "Marina District": 21,
        "Richmond District": 12,
        "Financial District": 30,
        "Embarcadero": 30,
        "The Castro": 17,
        "Alamo Square": 17,
        "Presidio": 16
    },
    "Union Square": {
        "Russian Hill": 13,
        "Sunset District": 27,
        "Nob Hill": 9,
        "Marina District": 18,
        "Richmond District": 20,
        "Financial District": 9,
        "Embarcadero": 11,
        "The Castro": 17,
        "Alamo Square": 15,
        "Presidio": 24
    },
    "Nob Hill": {
        "Russian Hill": 5,
        "Sunset District": 24,
        "Union Square": 7,
        "Marina District": 11,
        "Richmond District": 14,
        "Financial District": 9,
        "Embarcadero": 9,
        "The Castro": 17,
        "Alamo Square": 11,
        "Presidio": 17
    },
    "Marina District": {
        "Russian Hill": 8,
        "Sunset District": 19,
        "Union Square": 16,
        "Nob Hill": 12,
        "Richmond District": 11,
        "Financial District": 17,
        "Embarcadero": 14,
        "The Castro": 22,
        "Alamo Square": 15,
        "Presidio": 10
    },
    "Richmond District": {
        "Russian Hill": 13,
        "Sunset District": 11,
        "Union Square": 21,
        "Nob Hill": 17,
        "Marina District": 9,
        "Financial District": 22,
        "Embarcadero": 19,
        "The Castro": 16,
        "Alamo Square": 13,
        "Presidio": 7
    },
    "Financial District": {
        "Russian Hill": 11,
        "Sunset District": 30,
        "Union Square": 9,
        "Nob Hill": 8,
        "Marina District": 15,
        "Richmond District": 21,
        "Embarcadero": 4,
        "The Castro": 20,
        "Alamo Square": 17,
        "Presidio": 22
    },
    "Embarcadero": {
        "Russian Hill": 8,
        "Sunset District": 30,
        "Union Square": 10,
        "Nob Hill": 10,
        "Marina District": 12,
        "Richmond District": 21,
        "Financial District": 5,
        "The Castro": 25,
        "Alamo Square": 19,
        "Presidio": 20
    },
    "The Castro": {
        "Russian Hill": 18,
        "Sunset District": 17,
        "Union Square": 19,
        "Nob Hill": 16,
        "Marina District": 21,
        "Richmond District": 16,
        "Financial District": 21,
        "Embarcadero": 22,
        "Alamo Square": 8,
        "Presidio": 20
    },
    "Alamo Square": {
        "Russian Hill": 13,
        "Sunset District": 16,
        "Union Square": 14,
        "Nob Hill": 11,
        "Marina District": 15,
        "Richmond District": 11,
        "Financial District": 17,
        "Embarcadero": 16,
        "The Castro": 8,
        "Presidio": 17
    },
    "Presidio": {
        "Russian Hill": 14,
        "Sunset District": 15,
        "Union Square": 22,
        "Nob Hill": 18,
        "Marina District": 11,
        "Richmond District": 7,
        "Financial District": 23,
        "Embarcadero": 20,
        "The Castro": 21,
        "Alamo Square": 19
    }
}

# Define friends with their constraints
friends = [
    {"name": "David", "location": "Sunset District", 
     "available_start": time_to_minutes("9:15AM"), 
     "available_end": time_to_minutes("10:00PM"), 
     "required_duration": 15},
    {"name": "Kenneth", "location": "Union Square", 
     "available_start": time_to_minutes("9:15PM"), 
     "available_end": time_to_minutes("9:45PM"), 
     "required_duration": 15},
    {"name": "Patricia", "location": "Nob Hill", 
     "available_start": time_to_minutes("3:00PM"), 
     "available_end": time_to_minutes("7:15PM"), 
     "required_duration": 120},
    {"name": "Mary", "location": "Marina District", 
     "available_start": time_to_minutes("2:45PM"), 
     "available_end": time_to_minutes("4:45PM"), 
     "required_duration": 45},
    {"name": "Charles", "location": "Richmond District", 
     "available_start": time_to_minutes("5:15PM"), 
     "available_end": time_to_minutes("9:00PM"), 
     "required_duration": 15},
    {"name": "Joshua", "location": "Financial District", 
     "available_start": time_to_minutes("2:30PM"), 
     "available_end": time_to_minutes("5:15PM"), 
     "required_duration": 90},
    {"name": "Ronald", "location": "Embarcadero", 
     "available_start": time_to_minutes("6:15PM"), 
     "available_end": time_to_minutes("8:45PM"), 
     "required_duration": 30},
    {"name": "George", "location": "The Castro", 
     "available_start": time_to_minutes("2:15PM"), 
     "available_end": time_to_minutes("7:00PM"), 
     "required_duration": 105},
    {"name": "Kimberly", "location": "Alamo Square", 
     "available_start": time_to_minutes("9:00AM"), 
     "available_end": time_to_minutes("2:30PM"), 
     "required_duration": 105},
    {"name": "William", "location": "Presidio", 
     "available_start": time_to_minutes("7:00AM"), 
     "available_end": time_to_minutes("12:45PM"), 
     "required_duration": 60}
]

n = len(friends)
num_masks = 1 << n
INF = 10**9

# dp[mask][last] for last in [0, 10] (0..9 for friends, 10 for dummy)
dp = [[INF] * 11 for _ in range(num_masks)]
parent = [[None] * 11 for _ in range(num_masks)]  # (prev_mask, prev_last, start, end)

# Initialize: dummy state (mask=0, last=10) -> start at Russian Hill at 540 minutes (9:00AM)
dp[0][10] = 540

# DP over masks and last state
for mask in range(num_masks):
    for last in range(11):  # last: 0..9 for friends, 10 for dummy
        if dp[mask][last] == INF:
            continue
            
        # Determine current location
        if last == 10:  # dummy state -> at Russian Hill
            current_loc = "Russian Hill"
        else:
            current_loc = friends[last]["location"]
        
        # Try to extend to every unvisited friend
        for j in range(n):
            if mask & (1 << j):
                continue
                
            next_loc = friends[j]["location"]
            travel = travel_times[current_loc][next_loc]
            arrival = dp[mask][last] + travel
            start_time = max(arrival, friends[j]["available_start"])
            end_time = start_time + friends[j]["required_duration"]
            
            if end_time <= friends[j]["available_end"]:
                new_mask = mask | (1 << j)
                if end_time < dp[new_mask][j]:
                    dp[new_mask][j] = end_time
                    parent[new_mask][j] = (mask, last, start_time, end_time)

# Find state with maximum number of meetings
best_count = -1
best_mask = None
best_last = None
for mask in range(num_masks):
    for last in range(10):  # only real friends (0..9)
        if dp[mask][last] < INF:
            count = bin(mask).count("1")
            if count > best_count:
                best_count = count
                best_mask = mask
                best_last = last

# Reconstruct itinerary
itinerary = []
current_mask = best_mask
current_last = best_last
while current_mask != 0:
    prev_mask, prev_last, start, end = parent[current_mask][current_last]
    friend = friends[current_last]
    itinerary.append({
        "action": "meet",
        "location": friend["location"],
        "person": friend["name"],
        "start_time": minutes_to_time(start),
        "end_time": minutes_to_time(end)
    })
    current_mask = prev_mask
    current_last = prev_last

# Reverse to get chronological order
itinerary.reverse()

# Output as JSON
result = {"itinerary": itinerary}
print(json.dumps(result))