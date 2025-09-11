import json

class Friend:
    def __init__(self, name, location, available_start, available_end, min_duration):
        self.name = name
        self.location = location
        self.available_start = available_start
        self.available_end = available_end
        self.min_duration = min_duration

def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

def main():
    travel_times = {
        "Nob Hill": {
            "Embarcadero": 9, "The Castro": 17, "Haight-Ashbury": 13, "Union Square": 7,
            "North Beach": 8, "Pacific Heights": 8, "Chinatown": 6, "Golden Gate Park": 17,
            "Marina District": 11, "Russian Hill": 5
        },
        "Embarcadero": {
            "Nob Hill": 10, "The Castro": 25, "Haight-Ashbury": 21, "Union Square": 10,
            "North Beach": 5, "Pacific Heights": 11, "Chinatown": 7, "Golden Gate Park": 25,
            "Marina District": 12, "Russian Hill": 8
        },
        "The Castro": {
            "Nob Hill": 16, "Embarcadero": 22, "Haight-Ashbury": 6, "Union Square": 19,
            "North Beach": 20, "Pacific Heights": 16, "Chinatown": 22, "Golden Gate Park": 11,
            "Marina District": 21, "Russian Hill": 18
        },
        "Haight-Ashbury": {
            "Nob Hill": 15, "Embarcadero": 20, "The Castro": 6, "Union Square": 19,
            "North Beach": 19, "Pacific Heights": 12, "Chinatown": 19, "Golden Gate Park": 7,
            "Marina District": 17, "Russian Hill": 17
        },
        "Union Square": {
            "Nob Hill": 9, "Embarcadero": 11, "The Castro": 17, "Haight-Ashbury": 18,
            "North Beach": 10, "Pacific Heights": 15, "Chinatown": 7, "Golden Gate Park": 22,
            "Marina District": 18, "Russian Hill": 13
        },
        "North Beach": {
            "Nob Hill": 7, "Embarcadero": 6, "The Castro": 23, "Haight-Ashbury": 18,
            "Union Square": 7, "Pacific Heights": 8, "Chinatown": 6, "Golden Gate Park": 22,
            "Marina District": 9, "Russian Hill": 4
        },
        "Pacific Heights": {
            "Nob Hill": 8, "Embarcadero": 10, "The Castro": 16, "Haight-Ashbury": 11,
            "Union Square": 12, "North Beach": 9, "Chinatown": 11, "Golden Gate Park": 15,
            "Marina District": 6, "Russian Hill": 7
        },
        "Chinatown": {
            "Nob Hill": 9, "Embarcadero": 5, "The Castro": 22, "Haight-Ashbury": 19,
            "Union Square": 7, "North Beach": 3, "Pacific Heights": 10, "Golden Gate Park": 23,
            "Marina District": 12, "Russian Hill": 7
        },
        "Golden Gate Park": {
            "Nob Hill": 20, "Embarcadero": 25, "The Castro": 13, "Haight-Ashbury": 7,
            "Union Square": 22, "North Beach": 23, "Pacific Heights": 16, "Chinatown": 23,
            "Marina District": 16, "Russian Hill": 19
        },
        "Marina District": {
            "Nob Hill": 12, "Embarcadero": 14, "The Castro": 22, "Haight-Ashbury": 16,
            "Union Square": 16, "North Beach": 11, "Pacific Heights": 7, "Chinatown": 15,
            "Golden Gate Park": 18, "Russian Hill": 8
        },
        "Russian Hill": {
            "Nob Hill": 5, "Embarcadero": 8, "The Castro": 21, "Haight-Ashbury": 17,
            "Union Square": 10, "North Beach": 5, "Pacific Heights": 7, "Chinatown": 9,
            "Golden Gate Park": 21, "Marina District": 7
        }
    }

    friends = [
        Friend("Mary", "Embarcadero", 20*60, 21*60+15, 75),
        Friend("Kenneth", "The Castro", 11*60+15, 19*60+15, 30),
        Friend("Joseph", "Haight-Ashbury", 20*60, 22*60, 120),
        Friend("Sarah", "Union Square", 11*60+45, 14*60+30, 90),
        Friend("Thomas", "North Beach", 19*60+15, 19*60+45, 15),
        Friend("Daniel", "Pacific Heights", 13*60+45, 20*60+30, 15),
        Friend("Richard", "Chinatown", 8*60, 18*60+45, 30),
        Friend("Mark", "Golden Gate Park", 17*60+30, 21*60+30, 120),
        Friend("David", "Marina District", 20*60, 21*60, 60),
        Friend("Karen", "Russian Hill", 13*60+15, 18*60+30, 120)
    ]

    n = len(friends)
    num_states = 1 << n
    INF = 10**9
    dp = [[INF] * n for _ in range(num_states)]
    parent_mask = [[0] * n for _ in range(num_states)]
    parent_index = [[-1] * n for _ in range(num_states)]

    for i in range(n):
        travel = travel_times["Nob Hill"][friends[i].location]
        arrival = 540 + travel
        start_meeting = max(arrival, friends[i].available_start)
        end_meeting = start_meeting + friends[i].min_duration
        if end_meeting <= friends[i].available_end:
            dp[1 << i][i] = end_meeting
            parent_mask[1 << i][i] = 0
            parent_index[1 << i][i] = -1

    for mask in range(num_states):
        for i in range(n):
            if dp[mask][i] == INF:
                continue
            for j in range(n):
                if mask & (1 << j):
                    continue
                travel = travel_times[friends[i].location][friends[j].location]
                arrival = dp[mask][i] + travel
                start_meeting = max(arrival, friends[j].available_start)
                end_meeting = start_meeting + friends[j].min_duration
                if end_meeting > friends[j].available_end:
                    continue
                new_mask = mask | (1 << j)
                if end_meeting < dp[new_mask][j]:
                    dp[new_mask][j] = end_meeting
                    parent_mask[new_mask][j] = mask
                    parent_index[new_mask][j] = i

    best_mask = 0
    best_count = 0
    best_j = -1
    for mask in range(num_states):
        for j in range(n):
            if dp[mask][j] < INF:
                count = bin(mask).count('1')
                if count > best_count or (count == best_count and dp[mask][j] < dp[best_mask][best_j]):
                    best_count = count
                    best_mask = mask
                    best_j = j

    itinerary = []
    mask = best_mask
    j = best_j
    while mask != 0:
        friend = friends[j]
        start_time = dp[mask][j] - friend.min_duration
        itinerary.append({
            "action": "meet",
            "location": friend.location,
            "person": friend.name,
            "start_time": minutes_to_time(start_time),
            "end_time": minutes_to_time(dp[mask][j])
        })
        prev_mask = parent_mask[mask][j]
        prev_j = parent_index[mask][j]
        mask = prev_mask
        j = prev_j

    itinerary.reverse()
    result = {"itinerary": itinerary}
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()