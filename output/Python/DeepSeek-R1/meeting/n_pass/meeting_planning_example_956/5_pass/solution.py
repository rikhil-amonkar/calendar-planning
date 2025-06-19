import json

def format_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

locations = [
    'The Castro',
    'Alamo Square',
    'Richmond District',
    'Financial District',
    'Union Square',
    'Fisherman\'s Wharf',
    'Marina District',
    'Haight-Ashbury',
    'Mission District',
    'Pacific Heights',
    'Golden Gate Park'
]

travel_dict = {
    "The Castro": {
        "Alamo Square": 8,
        "Richmond District": 16,
        "Financial District": 21,
        "Union Square": 19,
        "Fisherman's Wharf": 24,
        "Marina District": 21,
        "Haight-Ashbury": 6,
        "Mission District": 7,
        "Pacific Heights": 16,
        "Golden Gate Park": 11
    },
    "Alamo Square": {
        "The Castro": 8,
        "Richmond District": 11,
        "Financial District": 17,
        "Union Square": 14,
        "Fisherman's Wharf": 19,
        "Marina District": 15,
        "Haight-Ashbury": 5,
        "Mission District": 10,
        "Pacific Heights": 10,
        "Golden Gate Park": 9
    },
    "Richmond District": {
        "The Castro": 16,
        "Alamo Square": 13,
        "Financial District": 22,
        "Union Square": 21,
        "Fisherman's Wharf": 18,
        "Marina District": 9,
        "Haight-Ashbury": 10,
        "Mission District": 20,
        "Pacific Heights": 10,
        "Golden Gate Park": 9
    },
    "Financial District": {
        "The Castro": 20,
        "Alamo Square": 17,
        "Richmond District": 21,
        "Union Square": 9,
        "Fisherman's Wharf": 10,
        "Marina District": 15,
        "Haight-Ashbury": 19,
        "Mission District": 17,
        "Pacific Heights": 13,
        "Golden Gate Park": 23
    },
    "Union Square": {
        "The Castro": 17,
        "Alamo Square": 15,
        "Richmond District": 20,
        "Financial District": 9,
        "Fisherman's Wharf": 15,
        "Marina District": 18,
        "Haight-Ashbury": 18,
        "Mission District": 14,
        "Pacific Heights": 15,
        "Golden Gate Park": 22
    },
    "Fisherman's Wharf": {
        "The Castro": 27,
        "Alamo Square": 21,
        "Richmond District": 18,
        "Financial District": 11,
        "Union Square": 13,
        "Marina District": 9,
        "Haight-Ashbury": 22,
        "Mission District": 22,
        "Pacific Heights": 12,
        "Golden Gate Park": 25
    },
    "Marina District": {
        "The Castro": 22,
        "Alamo Square": 15,
        "Richmond District": 11,
        "Financial District": 17,
        "Union Square": 16,
        "Fisherman's Wharf": 10,
        "Haight-Ashbury": 16,
        "Mission District": 20,
        "Pacific Heights": 7,
        "Golden Gate Park": 18
    },
    "Haight-Ashbury": {
        "The Castro": 6,
        "Alamo Square": 5,
        "Richmond District": 10,
        "Financial District": 21,
        "Union Square": 19,
        "Fisherman's Wharf": 23,
        "Marina District": 17,
        "Mission District": 11,
        "Pacific Heights": 12,
        "Golden Gate Park": 7
    },
    "Mission District": {
        "The Castro": 7,
        "Alamo Square": 11,
        "Richmond District": 20,
        "Financial District": 15,
        "Union Square": 15,
        "Fisherman's Wharf": 22,
        "Marina District": 19,
        "Haight-Ashbury": 12,
        "Pacific Heights": 16,
        "Golden Gate Park": 17
    },
    "Pacific Heights": {
        "The Castro": 16,
        "Alamo Square": 10,
        "Richmond District": 12,
        "Financial District": 13,
        "Union Square": 12,
        "Fisherman's Wharf": 13,
        "Marina District": 6,
        "Haight-Ashbury": 11,
        "Mission District": 15,
        "Golden Gate Park": 15
    },
    "Golden Gate Park": {
        "The Castro": 13,
        "Alamo Square": 9,
        "Richmond District": 7,
        "Financial District": 26,
        "Union Square": 22,
        "Fisherman's Wharf": 24,
        "Marina District": 16,
        "Haight-Ashbury": 7,
        "Mission District": 17,
        "Pacific Heights": 16
    }
}

travel = [[0] * 11 for _ in range(11)]
for i in range(11):
    for j in range(11):
        if i == j:
            travel[i][j] = 0
        else:
            loc_i = locations[i]
            loc_j = locations[j]
            travel[i][j] = travel_dict[loc_i][loc_j]

friends = [
    {'name': 'William', 'location_index': 1, 'start': 15*60+15, 'end': 17*60+15, 'min_duration': 60},
    {'name': 'Joshua', 'location_index': 2, 'start': 7*60, 'end': 20*60, 'min_duration': 15},
    {'name': 'Joseph', 'location_index': 3, 'start': 11*60+15, 'end': 13*60+30, 'min_duration': 15},
    {'name': 'David', 'location_index': 4, 'start': 16*60+45, 'end': 19*60+15, 'min_duration': 45},
    {'name': 'Brian', 'location_index': 5, 'start': 13*60+45, 'end': 20*60+45, 'min_duration': 105},
    {'name': 'Karen', 'location_index': 6, 'start': 11*60+30, 'end': 18*60+30, 'min_duration': 15},
    {'name': 'Anthony', 'location_index': 7, 'start': 7*60+15, 'end': 10*60+30, 'min_duration': 30},
    {'name': 'Matthew', 'location_index': 8, 'start': 17*60+15, 'end': 19*60+15, 'min_duration': 120},
    {'name': 'Helen', 'location_index': 9, 'start': 8*60, 'end': 12*60, 'min_duration': 75},
    {'name': 'Jeffrey', 'location_index': 10, 'start': 19*60, 'end': 21*60+30, 'min_duration': 60}
]

n = len(friends)
dp = [[None] * 11 for _ in range(1<<n)]
dp[0][0] = (540, None, None, None, None, None)

for bitmask in range(1<<n):
    for loc_index in range(11):
        if dp[bitmask][loc_index] is None:
            continue
        current_time, _, _, _, _, _ = dp[bitmask][loc_index]
        for next_friend in range(n):
            if bitmask & (1 << next_friend):
                continue
            next_loc_index = friends[next_friend]['location_index']
            travel_time = travel[loc_index][next_loc_index]
            arrival_time = current_time + travel_time
            friend_start = friends[next_friend]['start']
            friend_end = friends[next_friend]['end']
            min_duration = friends[next_friend]['min_duration']
            start_meeting = max(arrival_time, friend_start)
            end_meeting = start_meeting + min_duration
            if end_meeting > friend_end:
                continue
            new_bitmask = bitmask | (1 << next_friend)
            current_val = dp[new_bitmask][next_loc_index]
            if current_val is None or end_meeting < current_val[0]:
                dp[new_bitmask][next_loc_index] = (end_meeting, bitmask, loc_index, next_friend, start_meeting, end_meeting)

best_count = -1
best_bitmask = None
best_loc_index = None
best_state = None
for bitmask in range(1<<n):
    count = bin(bitmask).count("1")
    for loc_index in range(11):
        state = dp[bitmask][loc_index]
        if state is None:
            continue
        current_time = state[0]
        travel_time_back = travel[loc_index][0]
        if current_time + travel_time_back > 1260:
            continue
        if count > best_count:
            best_count = count
            best_bitmask = bitmask
            best_loc_index = loc_index
            best_state = state

itinerary = []
bitmask = best_bitmask
loc_index = best_loc_index
state = best_state
while state is not None and state[1] is not None:
    end_time, prev_bitmask, prev_loc_index, friend_index, start_meeting, end_meeting = state
    friend = friends[friend_index]
    meeting = {
        "action": "meet",
        "location": locations[friend['location_index']],
        "person": friend['name'],
        "start_time": format_time(start_meeting),
        "end_time": format_time(end_meeting)
    }
    itinerary.append(meeting)
    bitmask = prev_bitmask
    loc_index = prev_loc_index
    state = dp[bitmask][loc_index] if bitmask != 0 or loc_index != 0 else None

itinerary.reverse()

result = {
    "itinerary": itinerary
}

print(json.dumps(result))