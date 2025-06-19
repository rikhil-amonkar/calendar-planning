import json

def min_to_time(m):
    hour = m // 60
    minute = m % 60
    return f"{hour}:{minute:02d}"

def main():
    travel_dict = {
        "Nob Hill": {
            "Embarcadero": 9,
            "The Castro": 17,
            "Haight-Ashbury": 13,
            "Union Square": 7,
            "North Beach": 8,
            "Pacific Heights": 8,
            "Chinatown": 6,
            "Golden Gate Park": 17,
            "Marina District": 11,
            "Russian Hill": 5
        },
        "Embarcadero": {
            "Nob Hill": 10,
            "The Castro": 25,
            "Haight-Ashbury": 21,
            "Union Square": 10,
            "North Beach": 5,
            "Pacific Heights": 11,
            "Chinatown": 7,
            "Golden Gate Park": 25,
            "Marina District": 12,
            "Russian Hill": 8
        },
        "The Castro": {
            "Nob Hill": 16,
            "Embarcadero": 22,
            "Haight-Ashbury": 6,
            "Union Square": 19,
            "North Beach": 20,
            "Pacific Heights": 16,
            "Chinatown": 22,
            "Golden Gate Park": 13,
            "Marina District": 21,
            "Russian Hill": 18
        },
        "Haight-Ashbury": {
            "Nob Hill": 15,
            "Embarcadero": 20,
            "The Castro": 6,
            "Union Square": 19,
            "North Beach": 19,
            "Pacific Heights": 12,
            "Chinatown": 19,
            "Golden Gate Park": 7,
            "Marina District": 17,
            "Russian Hill": 17
        },
        "Union Square": {
            "Nob Hill": 9,
            "Embarcadero": 11,
            "The Castro": 17,
            "Haight-Ashbury": 18,
            "North Beach": 10,
            "Pacific Heights": 15,
            "Chinatown": 7,
            "Golden Gate Park": 22,
            "Marina District": 18,
            "Russian Hill": 13
        },
        "North Beach": {
            "Nob Hill": 7,
            "Embarcadero": 6,
            "The Castro": 23,
            "Haight-Ashbury": 18,
            "Union Square": 7,
            "Pacific Heights": 8,
            "Chinatown": 6,
            "Golden Gate Park": 22,
            "Marina District": 9,
            "Russian Hill": 4
        },
        "Pacific Heights": {
            "Nob Hill": 8,
            "Embarcadero": 10,
            "The Castro": 16,
            "Haight-Ashbury": 11,
            "Union Square": 12,
            "North Beach": 9,
            "Chinatown": 11,
            "Golden Gate Park": 15,
            "Marina District": 6,
            "Russian Hill": 7
        },
        "Chinatown": {
            "Nob Hill": 9,
            "Embarcadero": 5,
            "The Castro": 22,
            "Haight-Ashbury": 19,
            "Union Square": 7,
            "North Beach": 3,
            "Pacific Heights": 10,
            "Golden Gate Park": 23,
            "Marina District": 12,
            "Russian Hill": 7
        },
        "Golden Gate Park": {
            "Nob Hill": 20,
            "Embarcadero": 25,
            "The Castro": 13,
            "Haight-Ashbury": 7,
            "Union Square": 22,
            "North Beach": 23,
            "Pacific Heights": 16,
            "Chinatown": 23,
            "Marina District": 16,
            "Russian Hill": 19
        },
        "Marina District": {
            "Nob Hill": 12,
            "Embarcadero": 14,
            "The Castro": 22,
            "Haight-Ashbury": 16,
            "Union Square": 16,
            "North Beach": 11,
            "Pacific Heights": 7,
            "Chinatown": 15,
            "Golden Gate Park": 18,
            "Russian Hill": 8
        },
        "Russian Hill": {
            "Nob Hill": 5,
            "Embarcadero": 8,
            "The Castro": 21,
            "Haight-Ashbury": 17,
            "Union Square": 10,
            "North Beach": 5,
            "Pacific Heights": 7,
            "Chinatown": 9,
            "Golden Gate Park": 21,
            "Marina District": 7
        }
    }

    locations = [
        "Nob Hill",
        "Embarcadero",
        "The Castro",
        "Haight-Ashbury",
        "Union Square",
        "North Beach",
        "Pacific Heights",
        "Chinatown",
        "Golden Gate Park",
        "Marina District",
        "Russian Hill"
    ]
    location_to_index = {loc: idx for idx, loc in enumerate(locations)}

    friends = [
        {"name": "Mary", "location": "Embarcadero", "start_avail": 20*60, "end_avail": 21*60+15, "min_dur": 75},
        {"name": "Kenneth", "location": "The Castro", "start_avail": 11*60+15, "end_avail": 19*60+15, "min_dur": 30},
        {"name": "Joseph", "location": "Haight-Ashbury", "start_avail": 20*60, "end_avail": 22*60, "min_dur": 120},
        {"name": "Sarah", "location": "Union Square", "start_avail": 11*60+45, "end_avail": 14*60+30, "min_dur": 90},
        {"name": "Thomas", "location": "North Beach", "start_avail": 19*60+15, "end_avail": 19*60+45, "min_dur": 15},
        {"name": "Daniel", "location": "Pacific Heights", "start_avail": 13*60+45, "end_avail": 20*60+30, "min_dur": 15},
        {"name": "Richard", "location": "Chinatown", "start_avail": 8*60, "end_avail": 18*60+45, "min_dur": 30},
        {"name": "Mark", "location": "Golden Gate Park", "start_avail": 17*60+30, "end_avail": 21*60+30, "min_dur": 120},
        {"name": "David", "location": "Marina District", "start_avail": 20*60, "end_avail": 21*60, "min_dur": 60},
        {"name": "Karen", "location": "Russian Hill", "start_avail": 13*60+15, "end_avail": 18*60+30, "min_dur": 120}
    ]

    n_locations = len(locations)
    n_friends = len(friends)
    BIG = 10**9

    travel_matrix = [[0] * n_locations for _ in range(n_locations)]
    for i in range(n_locations):
        for j in range(n_locations):
            if i == j:
                travel_matrix[i][j] = 0
            else:
                val1 = travel_dict[locations[i]][locations[j]]
                val2 = travel_dict[locations[j]][locations[i]]
                travel_matrix[i][j] = min(val1, val2)

    dp = [[BIG] * n_locations for _ in range(1 << n_friends)]
    parent = [[None] * n_locations for _ in range(1 << n_friends)]

    start_time = 9 * 60
    start_loc = location_to_index["Nob Hill"]
    dp[0][start_loc] = start_time

    for mask in range(1 << n_friends):
        for loc_idx in range(n_locations):
            if dp[mask][loc_idx] >= BIG:
                continue
            for friend_idx in range(n_friends):
                if mask & (1 << friend_idx):
                    continue
                friend = friends[friend_idx]
                to_loc = location_to_index[friend["location"]]
                travel_time = travel_matrix[loc_idx][to_loc]
                current_time = dp[mask][loc_idx]
                arrival_time = current_time + travel_time
                start_meeting = max(arrival_time, friend["start_avail"])
                end_meeting = start_meeting + friend["min_dur"]
                if end_meeting > friend["end_avail"]:
                    continue
                new_mask = mask | (1 << friend_idx)
                if end_meeting < dp[new_mask][to_loc]:
                    dp[new_mask][to_loc] = end_meeting
                    parent[new_mask][to_loc] = (mask, loc_idx, friend_idx, start_meeting, end_meeting)

    best_mask = None
    best_loc = None
    max_count = -1
    for mask in range(1 << n_friends):
        count = bin(mask).count("1")
        for loc in range(n_locations):
            if dp[mask][loc] < BIG:
                if count > max_count:
                    max_count = count
                    best_mask = mask
                    best_loc = loc

    meetings = []
    current_mask = best_mask
    current_loc = best_loc
    while current_mask != 0:
        if parent[current_mask][current_loc] is None:
            break
        prev_mask, prev_loc, friend_idx, start_meeting, end_meeting = parent[current_mask][current_loc]
        friend = friends[friend_idx]
        meetings.append({
            "action": "meet",
            "location": friend["location"],
            "person": friend["name"],
            "start_time": min_to_time(start_meeting),
            "end_time": min_to_time(end_meeting)
        })
        current_mask = prev_mask
        current_loc = prev_loc

    meetings.reverse()
    result = {"itinerary": meetings}
    print(json.dumps(result))

if __name__ == "__main__":
    main()