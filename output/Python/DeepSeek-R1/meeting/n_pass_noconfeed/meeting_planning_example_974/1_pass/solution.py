import json

def time_str_to_minutes(s):
    parts = s.split(':')
    hour = int(parts[0])
    rest = parts[1]
    minutes_str = rest[:-2]
    period = rest[-2:]
    minutes = int(minutes_str)
    if period == 'PM' and hour != 12:
        hour += 12
    if period == 'AM' and hour == 12:
        hour = 0
    total_minutes_since_midnight = hour * 60 + minutes
    return total_minutes_since_midnight - 9 * 60

def minutes_to_time(m):
    total_minutes_from_midnight = 9 * 60 + m
    hour = total_minutes_from_midnight // 60
    minute = total_minutes_from_midnight % 60
    return f"{hour}:{minute:02d}"

location_names = [
    "Sunset District",
    "Presidio",
    "Nob Hill",
    "Pacific Heights",
    "Mission District",
    "Marina District",
    "North Beach",
    "Russian Hill",
    "Richmond District",
    "Embarcadero",
    "Alamo Square"
]

location_to_index = {name: idx for idx, name in enumerate(location_names)}

travel_dict = {
    "Sunset District": {
        "Presidio": 16,
        "Nob Hill": 27,
        "Pacific Heights": 21,
        "Mission District": 25,
        "Marina District": 21,
        "North Beach": 28,
        "Russian Hill": 24,
        "Richmond District": 12,
        "Embarcadero": 30,
        "Alamo Square": 17
    },
    "Presidio": {
        "Sunset District": 15,
        "Nob Hill": 18,
        "Pacific Heights": 11,
        "Mission District": 26,
        "Marina District": 11,
        "North Beach": 18,
        "Russian Hill": 14,
        "Richmond District": 7,
        "Embarcadero": 20,
        "Alamo Square": 19
    },
    "Nob Hill": {
        "Sunset District": 24,
        "Presidio": 17,
        "Pacific Heights": 8,
        "Mission District": 13,
        "Marina District": 11,
        "North Beach": 8,
        "Russian Hill": 5,
        "Richmond District": 14,
        "Embarcadero": 9,
        "Alamo Square": 11
    },
    "Pacific Heights": {
        "Sunset District": 21,
        "Presidio": 11,
        "Nob Hill": 8,
        "Mission District": 15,
        "Marina District": 6,
        "North Beach": 9,
        "Russian Hill": 7,
        "Richmond District": 12,
        "Embarcadero": 10,
        "Alamo Square": 10
    },
    "Mission District": {
        "Sunset District": 24,
        "Presidio": 25,
        "Nob Hill": 12,
        "Pacific Heights": 16,
        "Marina District": 19,
        "North Beach": 17,
        "Russian Hill": 15,
        "Richmond District": 20,
        "Embarcadero": 19,
        "Alamo Square": 11
    },
    "Marina District": {
        "Sunset District": 19,
        "Presidio": 10,
        "Nob Hill": 12,
        "Pacific Heights": 7,
        "Mission District": 20,
        "North Beach": 11,
        "Russian Hill": 8,
        "Richmond District": 11,
        "Embarcadero": 14,
        "Alamo Square": 15
    },
    "North Beach": {
        "Sunset District": 27,
        "Presidio": 17,
        "Nob Hill": 7,
        "Pacific Heights": 8,
        "Mission District": 18,
        "Marina District": 9,
        "Russian Hill": 4,
        "Richmond District": 18,
        "Embarcadero": 6,
        "Alamo Square": 16
    },
    "Russian Hill": {
        "Sunset District": 23,
        "Presidio": 14,
        "Nob Hill": 5,
        "Pacific Heights": 7,
        "Mission District": 16,
        "Marina District": 7,
        "North Beach": 5,
        "Richmond District": 14,
        "Embarcadero": 8,
        "Alamo Square": 15
    },
    "Richmond District": {
        "Sunset District": 11,
        "Presidio": 7,
        "Nob Hill": 17,
        "Pacific Heights": 10,
        "Mission District": 20,
        "Marina District": 9,
        "North Beach": 17,
        "Russian Hill": 13,
        "Embarcadero": 19,
        "Alamo Square": 13
    },
    "Embarcadero": {
        "Sunset District": 30,
        "Presidio": 20,
        "Nob Hill": 10,
        "Pacific Heights": 11,
        "Mission District": 20,
        "Marina District": 12,
        "North Beach": 5,
        "Russian Hill": 8,
        "Richmond District": 21,
        "Alamo Square": 19
    },
    "Alamo Square": {
        "Sunset District": 16,
        "Presidio": 17,
        "Nob Hill": 11,
        "Pacific Heights": 10,
        "Mission District": 10,
        "Marina District": 15,
        "North Beach": 15,
        "Russian Hill": 13,
        "Richmond District": 11,
        "Embarcadero": 16
    }
}

n_locations = len(location_names)
travel_time = [[0] * n_locations for _ in range(n_locations)]
for i, from_loc in enumerate(location_names):
    for j, to_loc in enumerate(location_names):
        if from_loc == to_loc:
            travel_time[i][j] = 0
        else:
            travel_time[i][j] = travel_dict[from_loc][to_loc]

friends = [
    {"name": "Charles", "location": "Presidio", "available_start": "1:15PM", "available_end": "3:00PM", "min_duration": 105},
    {"name": "Robert", "location": "Nob Hill", "available_start": "1:15PM", "available_end": "5:30PM", "min_duration": 90},
    {"name": "Nancy", "location": "Pacific Heights", "available_start": "2:45PM", "available_end": "10:00PM", "min_duration": 105},
    {"name": "Brian", "location": "Mission District", "available_start": "3:30PM", "available_end": "10:00PM", "min_duration": 60},
    {"name": "Kimberly", "location": "Marina District", "available_start": "5:00PM", "available_end": "7:45PM", "min_duration": 75},
    {"name": "David", "location": "North Beach", "available_start": "2:45PM", "available_end": "4:30PM", "min_duration": 75},
    {"name": "William", "location": "Russian Hill", "available_start": "12:30PM", "available_end": "7:15PM", "min_duration": 120},
    {"name": "Jeffrey", "location": "Richmond District", "available_start": "12:00PM", "available_end": "7:15PM", "min_duration": 45},
    {"name": "Karen", "location": "Embarcadero", "available_start": "2:15PM", "available_end": "8:45PM", "min_duration": 60},
    {"name": "Joshua", "location": "Alamo Square", "available_start": "6:45PM", "available_end": "10:00PM", "min_duration": 60}
]

for friend in friends:
    friend['start_minutes'] = time_str_to_minutes(friend['available_start'])
    friend['end_minutes'] = time_str_to_minutes(friend['available_end'])
    friend['location_index'] = location_to_index[friend['location']]

n_friends = len(friends)
n_states = 1 << n_friends
INF = 10**9
dp = [[INF] * n_locations for _ in range(n_states)]
parent = [[None] * n_locations for _ in range(n_states)]

dp[0][0] = 0

for state in range(n_states):
    for loc in range(n_locations):
        if dp[state][loc] == INF:
            continue
        for j in range(n_friends):
            if state & (1 << j):
                continue
            friend_j = friends[j]
            loc_j = friend_j['location_index']
            tt = travel_time[loc][loc_j]
            arrive_time = dp[state][loc] + tt
            start_meet = max(arrive_time, friend_j['start_minutes'])
            end_meet = start_meet + friend_j['min_duration']
            if end_meet <= friend_j['end_minutes']:
                new_state = state | (1 << j)
                if end_meet < dp[new_state][loc_j]:
                    dp[new_state][loc_j] = end_meet
                    parent[new_state][loc_j] = (state, loc, j, start_meet, end_meet)

best_state = 0
best_count = 0
best_loc = None
for state in range(n_states):
    count = bin(state).count("1")
    for loc in range(n_locations):
        if dp[state][loc] < INF:
            if count > best_count:
                best_count = count
                best_state = state
                best_loc = loc

itinerary = []
current_state = best_state
current_loc = best_loc
while current_state != 0:
    if parent[current_state][current_loc] is None:
        break
    prev_state, prev_loc, j, start_meet, end_meet = parent[current_state][current_loc]
    friend_j = friends[j]
    start_str = minutes_to_time(start_meet)
    end_str = minutes_to_time(end_meet)
    itinerary.append({
        "action": "meet",
        "location": friend_j['location'],
        "person": friend_j['name'],
        "start_time": start_str,
        "end_time": end_str
    })
    current_state = prev_state
    current_loc = prev_loc

itinerary.reverse()
result = {"itinerary": itinerary}
print(json.dumps(result))