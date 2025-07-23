import json

def min_to_time(m):
    hours = m // 60
    minutes = m % 60
    hour = 9 + hours
    return f"{hour}:{minutes:02d}"

travel_times = {
    "Embarcadero": {
        "Bayview": 21,
        "Chinatown": 7,
        "Alamo Square": 19,
        "Nob Hill": 10,
        "Presidio": 20,
        "Union Square": 10,
        "The Castro": 25,
        "North Beach": 5,
        "Fisherman's Wharf": 6,
        "Marina District": 12
    },
    "Bayview": {
        "Embarcadero": 19,
        "Chinatown": 19,
        "Alamo Square": 16,
        "Nob Hill": 20,
        "Presidio": 32,
        "Union Square": 18,
        "The Castro": 19,
        "North Beach": 22,
        "Fisherman's Wharf": 25,
        "Marina District": 27
    },
    "Chinatown": {
        "Embarcadero": 5,
        "Bayview": 20,
        "Alamo Square": 17,
        "Nob Hill": 9,
        "Presidio": 19,
        "Union Square": 7,
        "The Castro": 22,
        "North Beach": 3,
        "Fisherman's Wharf": 8,
        "Marina District": 12
    },
    "Alamo Square": {
        "Embarcadero": 16,
        "Bayview": 16,
        "Chinatown": 15,
        "Nob Hill": 11,
        "Presidio": 17,
        "Union Square": 14,
        "The Castro": 8,
        "North Beach": 15,
        "Fisherman's Wharf": 19,
        "Marina District": 15
    },
    "Nob Hill": {
        "Embarcadero": 9,
        "Bayview": 19,
        "Chinatown": 6,
        "Alamo Square": 11,
        "Presidio": 17,
        "Union Square": 7,
        "The Castro": 17,
        "North Beach": 8,
        "Fisherman's Wharf": 10,
        "Marina District": 11
    },
    "Presidio": {
        "Embarcadero": 20,
        "Bayview": 31,
        "Chinatown": 21,
        "Alamo Square": 19,
        "Nob Hill": 18,
        "Union Square": 22,
        "The Castro": 21,
        "North Beach": 18,
        "Fisherman's Wharf": 19,
        "Marina District": 11
    },
    "Union Square": {
        "Embarcadero": 11,
        "Bayview": 15,
        "Chinatown": 7,
        "Alamo Square": 15,
        "Nob Hill": 9,
        "Presidio": 24,
        "The Castro": 17,
        "North Beach": 10,
        "Fisherman's Wharf": 15,
        "Marina District": 18
    },
    "The Castro": {
        "Embarcadero": 22,
        "Bayview": 19,
        "Chinatown": 22,
        "Alamo Square": 8,
        "Nob Hill": 16,
        "Presidio": 20,
        "Union Square": 19,
        "North Beach": 20,
        "Fisherman's Wharf": 24,
        "Marina District": 21
    },
    "North Beach": {
        "Embarcadero": 6,
        "Bayview": 25,
        "Chinatown": 6,
        "Alamo Square": 16,
        "Nob Hill": 7,
        "Presidio": 17,
        "Union Square": 7,
        "The Castro": 23,
        "Fisherman's Wharf": 5,
        "Marina District": 9
    },
    "Fisherman's Wharf": {
        "Embarcadero": 8,
        "Bayview": 26,
        "Chinatown": 12,
        "Alamo Square": 21,
        "Nob Hill": 11,
        "Presidio": 17,
        "Union Square": 13,
        "The Castro": 27,
        "North Beach": 6,
        "Marina District": 9
    },
    "Marina District": {
        "Embarcadero": 14,
        "Bayview": 27,
        "Chinatown": 15,
        "Alamo Square": 15,
        "Nob Hill": 12,
        "Presidio": 10,
        "Union Square": 16,
        "The Castro": 22,
        "North Beach": 11,
        "Fisherman's Wharf": 10
    }
}

friends = [
    {"name": "Matthew", "location": "Bayview", "start": 615, "end": 780, "min_duration": 120},
    {"name": "Karen", "location": "Chinatown", "start": 615, "end": 735, "min_duration": 90},
    {"name": "Sarah", "location": "Alamo Square", "start": 660, "end": 765, "min_duration": 105},
    {"name": "Jessica", "location": "Nob Hill", "start": 450, "end": 585, "min_duration": 120},
    {"name": "Stephanie", "location": "Presidio", "start": 0, "end": 75, "min_duration": 60},
    {"name": "Mary", "location": "Union Square", "start": 465, "end": 750, "min_duration": 60},
    {"name": "Charles", "location": "The Castro", "start": 450, "end": 780, "min_duration": 105},
    {"name": "Nancy", "location": "North Beach", "start": 345, "end": 660, "min_duration": 15},
    {"name": "Thomas", "location": "Fisherman's Wharf", "start": 270, "end": 600, "min_duration": 30},
    {"name": "Brian", "location": "Marina District", "start": 195, "end": 540, "min_duration": 60},
]

n = len(friends)
memo = {}

def dfs(time, loc, mask):
    key = (time, loc, mask)
    if key in memo:
        return memo[key][0]
    
    best_count = 0
    best_i = None
    best_start = None
    best_end = None
    
    for i in range(n):
        if mask & (1 << i):
            continue
        friend = friends[i]
        try:
            travel = travel_times[loc][friend['location']]
        except KeyError:
            continue
        arrive_time = time + travel
        start_time = max(arrive_time, friend['start'])
        end_time = start_time + friend['min_duration']
        if end_time > friend['end']:
            continue
            
        new_time = end_time
        new_loc = friend['location']
        new_mask = mask | (1 << i)
        count_rest = dfs(new_time, new_loc, new_mask)
        total_count = 1 + count_rest
        if total_count > best_count:
            best_count = total_count
            best_i = i
            best_start = start_time
            best_end = end_time
            
    memo[key] = (best_count, best_i, best_start, best_end)
    return best_count

start_time = 0
start_loc = "Embarcadero"
start_mask = 0
total_meetings = dfs(start_time, start_loc, start_mask)

current_state = (start_time, start_loc, start_mask)
itinerary = []

while True:
    if current_state not in memo:
        break
    count, best_i, start, end = memo[current_state]
    if best_i is None:
        break
    friend = friends[best_i]
    event = {
        "action": "meet",
        "location": friend['location'],
        "person": friend['name'],
        "start_time": min_to_time(start),
        "end_time": min_to_time(end)
    }
    itinerary.append(event)
    new_time = end
    new_loc = friend['location']
    new_mask = current_state[2] | (1 << best_i)
    current_state = (new_time, new_loc, new_mask)

result = {
    "itinerary": itinerary
}
print(json.dumps(result))