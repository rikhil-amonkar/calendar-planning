import json

def time_str_to_minutes(s):
    ampm = s[-2:]
    time_str = s[:-2].strip()
    if ':' in time_str:
        parts = time_str.split(':')
        hour = int(parts[0])
        minute = int(parts[1])
    else:
        hour = int(time_str)
        minute = 0
    if ampm == 'PM' and hour != 12:
        hour += 12
    if ampm == 'AM' and hour == 12:
        hour = 0
    return hour * 60 + minute

def minutes_to_time(mins):
    hour = mins // 60
    minute = mins % 60
    ampm = "AM"
    if hour >= 12:
        ampm = "PM"
        if hour > 12:
            hour -= 12
    if hour == 0:
        hour = 12
    return f"{hour}:{minute:02d}{ampm}"

locations = [
    "Richmond District",
    "Union Square",
    "Nob Hill",
    "Fisherman's Wharf",
    "Golden Gate Park",
    "Embarcadero",
    "Financial District",
    "North Beach",
    "Presidio",
    "Marina District"
]

travel_data = [
    ("Marina District", "Richmond District", 11),
    ("Marina District", "Union Square", 16),
    ("Marina District", "Nob Hill", 12),
    ("Marina District", "Fisherman's Wharf", 10),
    ("Marina District", "Golden Gate Park", 18),
    ("Marina District", "Embarcadero", 14),
    ("Marina District", "Financial District", 17),
    ("Marina District", "North Beach", 11),
    ("Marina District", "Presidio", 10),
    ("Richmond District", "Marina District", 9),
    ("Richmond District", "Union Square", 21),
    ("Richmond District", "Nob Hill", 17),
    ("Richmond District", "Fisherman's Wharf", 18),
    ("Richmond District", "Golden Gate Park", 9),
    ("Richmond District", "Embarcadero", 19),
    ("Richmond District", "Financial District", 22),
    ("Richmond District", "North Beach", 17),
    ("Richmond District", "Presidio", 7),
    ("Union Square", "Marina District", 18),
    ("Union Square", "Richmond District", 20),
    ("Union Square", "Nob Hill", 9),
    ("Union Square", "Fisherman's Wharf", 15),
    ("Union Square", "Golden Gate Park", 22),
    ("Union Square", "Embarcadero", 11),
    ("Union Square", "Financial District", 9),
    ("Union Square", "North Beach", 10),
    ("Union Square", "Presidio", 24),
    ("Nob Hill", "Marina District", 11),
    ("Nob Hill", "Richmond District", 14),
    ("Nob Hill", "Union Square", 7),
    ("Nob Hill", "Fisherman's Wharf", 10),
    ("Nob Hill", "Golden Gate Park", 17),
    ("Nob Hill", "Embarcadero", 9),
    ("Nob Hill", "Financial District", 9),
    ("Nob Hill", "North Beach", 8),
    ("Nob Hill", "Presidio", 17),
    ("Fisherman's Wharf", "Marina District", 9),
    ("Fisherman's Wharf", "Richmond District", 18),
    ("Fisherman's Wharf", "Union Square", 13),
    ("Fisherman's Wharf", "Nob Hill", 11),
    ("Fisherman's Wharf", "Golden Gate Park", 25),
    ("Fisherman's Wharf", "Embarcadero", 8),
    ("Fisherman's Wharf", "Financial District", 11),
    ("Fisherman's Wharf", "North Beach", 6),
    ("Fisherman's Wharf", "Presidio", 17),
    ("Golden Gate Park", "Marina District", 16),
    ("Golden Gate Park", "Richmond District", 7),
    ("Golden Gate Park", "Union Square", 22),
    ("Golden Gate Park", "Nob Hill", 20),
    ("Golden Gate Park", "Fisherman's Wharf", 24),
    ("Golden Gate Park", "Embarcadero", 25),
    ("Golden Gate Park", "Financial District", 26),
    ("Golden Gate Park", "North Beach", 23),
    ("Golden Gate Park", "Presidio", 11),
    ("Embarcadero", "Marina District", 12),
    ("Embarcadero", "Richmond District", 21),
    ("Embarcadero", "Union Square", 10),
    ("Embarcadero", "Nob Hill", 10),
    ("Embarcadero", "Fisherman's Wharf", 6),
    ("Embarcadero", "Golden Gate Park", 25),
    ("Embarcadero", "Financial District", 5),
    ("Embarcadero", "North Beach", 5),
    ("Embarcadero", "Presidio", 20),
    ("Financial District", "Marina District", 15),
    ("Financial District", "Richmond District", 21),
    ("Financial District", "Union Square", 9),
    ("Financial District", "Nob Hill", 8),
    ("Financial District", "Fisherman's Wharf", 10),
    ("Financial District", "Golden Gate Park", 23),
    ("Financial District", "Embarcadero", 4),
    ("Financial District", "North Beach", 7),
    ("Financial District", "Presidio", 22),
    ("North Beach", "Marina District", 9),
    ("North Beach", "Richmond District", 18),
    ("North Beach", "Union Square", 7),
    ("North Beach", "Nob Hill", 7),
    ("North Beach", "Fisherman's Wharf", 5),
    ("North Beach", "Golden Gate Park", 22),
    ("North Beach", "Embarcadero", 6),
    ("North Beach", "Financial District", 8),
    ("North Beach", "Presidio", 17),
    ("Presidio", "Marina District", 11),
    ("Presidio", "Richmond District", 7),
    ("Presidio", "Union Square", 22),
    ("Presidio", "Nob Hill", 18),
    ("Presidio", "Fisherman's Wharf", 19),
    ("Presidio", "Golden Gate Park", 12),
    ("Presidio", "Embarcadero", 20),
    ("Presidio", "Financial District", 23),
    ("Presidio", "North Beach", 18)
]

travel_dict = {}
for item in travel_data:
    from_loc, to_loc, t = item
    travel_dict[(from_loc, to_loc)] = t

n = len(locations)
travel_matrix = [[0] * n for _ in range(n)]
for i in range(n):
    for j in range(n):
        from_name = locations[i]
        to_name = locations[j]
        if from_name == to_name:
            travel_matrix[i][j] = 0
        else:
            travel_matrix[i][j] = travel_dict[(from_name, to_name)]

friend_names = [
    "Stephanie",
    "William",
    "Elizabeth",
    "Joseph",
    "Anthony",
    "Barbara",
    "Carol",
    "Sandra",
    "Kenneth"
]

friend_locations = [
    "Richmond District",    # Stephanie
    "Union Square",         # William
    "Nob Hill",             # Elizabeth
    "Fisherman's Wharf",    # Joseph
    "Golden Gate Park",     # Anthony
    "Embarcadero",          # Barbara
    "Financial District",   # Carol
    "North Beach",          # Sandra
    "Presidio"              # Kenneth
]

friend_windows = [
    ("4:15PM", "9:30PM"),
    ("10:45AM", "5:30PM"),
    ("12:15PM", "3:00PM"),
    ("12:45PM", "2:00PM"),
    ("1:00PM", "8:30PM"),
    ("7:15PM", "8:30PM"),
    ("11:45AM", "4:15PM"),
    ("10:00AM", "12:30PM"),
    ("9:15PM", "10:15PM")
]

friend_start = [time_str_to_minutes(win[0]) for win in friend_windows]
friend_end = [time_str_to_minutes(win[1]) for win in friend_windows]
friend_duration = [75, 45, 105, 75, 75, 75, 60, 15, 45]

friend_loc_indices = [locations.index(loc) for loc in friend_locations]

n_friends = len(friend_names)
n_masks = 1 << n_friends
INF = 10**9

dp = [[INF] * n_masks for _ in range(n)]
parent = [[None] * n_masks for _ in range(n)]

start_loc = locations.index("Marina District")
start_mask = 0
dp[start_loc][start_mask] = 540

for mask in range(n_masks):
    for loc in range(n):
        if dp[loc][mask] < INF:
            for i in range(n_friends):
                if mask & (1 << i) == 0:
                    next_loc = friend_loc_indices[i]
                    travel_time = travel_matrix[loc][next_loc]
                    arrival_time = dp[loc][mask] + travel_time
                    s_i = friend_start[i]
                    e_i = friend_end[i]
                    d_i = friend_duration[i]
                    start_meeting = max(arrival_time, s_i)
                    end_meeting = start_meeting + d_i
                    if end_meeting <= e_i:
                        new_mask = mask | (1 << i)
                        if end_meeting < dp[next_loc][new_mask]:
                            dp[next_loc][new_mask] = end_meeting
                            parent[next_loc][new_mask] = (loc, mask, i, start_meeting, end_meeting, dp[loc][mask])

best_count = -1
best_mask = None
best_loc = None
for mask in range(n_masks):
    for loc in range(n):
        if dp[loc][mask] < INF:
            count = bin(mask).count("1")
            if count > best_count:
                best_count = count
                best_mask = mask
                best_loc = loc

itinerary_list = []
current_loc = best_loc
current_mask = best_mask
while current_mask != 0 and parent[current_loc][current_mask] is not None:
    prev_loc, prev_mask, friend_index, start_meeting, end_meeting, prev_time = parent[current_loc][current_mask]
    
    meeting = {
        "action": "meet",
        "location": friend_locations[friend_index],
        "person": friend_names[friend_index],
        "start_time": minutes_to_time(start_meeting),
        "end_time": minutes_to_time(end_meeting)
    }
    itinerary_list.append(meeting)
    
    travel_time = travel_matrix[prev_loc][friend_loc_indices[friend_index]]
    arrival_time = prev_time + travel_time
    travel_event = {
        "action": "travel",
        "start_time": minutes_to_time(prev_time),
        "end_time": minutes_to_time(arrival_time),
        "from": locations[prev_loc],
        "to": friend_locations[friend_index]
    }
    itinerary_list.append(travel_event)
    
    current_loc = prev_loc
    current_mask = prev_mask

itinerary_list.reverse()

result = {
    "itinerary": itinerary_list
}

print(json.dumps(result))