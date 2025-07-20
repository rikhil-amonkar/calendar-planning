import json

def time_to_minutes(time_str):
    period = time_str[-2:].upper()
    time_part = time_str[:-2]
    if ':' in time_part:
        hour_str, minute_str = time_part.split(':', 1)
    else:
        hour_str = time_part
        minute_str = '00'
    hour = int(hour_str)
    minute = int(minute_str)
    if period == 'PM' and hour != 12:
        hour += 12
    if period == 'AM' and hour == 12:
        hour = 0
    return hour * 60 + minute

def minutes_to_time(minutes):
    hours = minutes // 60
    minutes = minutes % 60
    return f"{hours}:{minutes:02d}"

def main():
    location_names = [
        "Bayview",
        "North Beach",
        "Fisherman's Wharf",
        "Haight-Ashbury",
        "Nob Hill",
        "Golden Gate Park",
        "Union Square",
        "Alamo Square",
        "Presidio",
        "Chinatown",
        "Pacific Heights"
    ]

    travel_dict = {
        "Bayview": {
            "North Beach": 22,
            "Fisherman's Wharf": 25,
            "Haight-Ashbury": 19,
            "Nob Hill": 20,
            "Golden Gate Park": 22,
            "Union Square": 18,
            "Alamo Square": 16,
            "Presidio": 32,
            "Chinatown": 19,
            "Pacific Heights": 23
        },
        "North Beach": {
            "Bayview": 25,
            "Fisherman's Wharf": 5,
            "Haight-Ashbury": 18,
            "Nob Hill": 7,
            "Golden Gate Park": 22,
            "Union Square": 7,
            "Alamo Square": 16,
            "Presidio": 17,
            "Chinatown": 6,
            "Pacific Heights": 8
        },
        "Fisherman's Wharf": {
            "Bayview": 26,
            "North Beach": 6,
            "Haight-Ashbury": 22,
            "Nob Hill": 11,
            "Golden Gate Park": 25,
            "Union Square": 13,
            "Alamo Square": 21,
            "Presidio": 17,
            "Chinatown": 12,
            "Pacific Heights": 12
        },
        "Haight-Ashbury": {
            "Bayview": 18,
            "North Beach": 19,
            "Fisherman's Wharf": 23,
            "Nob Hill": 15,
            "Golden Gate Park": 7,
            "Union Square": 19,
            "Alamo Square": 5,
            "Presidio": 15,
            "Chinatown": 19,
            "Pacific Heights": 12
        },
        "Nob Hill": {
            "Bayview": 19,
            "North Beach": 8,
            "Fisherman's Wharf": 10,
            "Haight-Ashbury": 13,
            "Golden Gate Park": 17,
            "Union Square": 7,
            "Alamo Square": 11,
            "Presidio": 17,
            "Chinatown": 6,
            "Pacific Heights": 8
        },
        "Golden Gate Park": {
            "Bayview": 23,
            "North Beach": 23,
            "Fisherman's Wharf": 24,
            "Haight-Ashbury": 7,
            "Nob Hill": 20,
            "Union Square": 22,
            "Alamo Square": 9,
            "Presidio": 11,
            "Chinatown": 23,
            "Pacific Heights": 16
        },
        "Union Square": {
            "Bayview": 15,
            "North Beach": 10,
            "Fisherman's Wharf": 15,
            "Haight-Ashbury": 18,
            "Nob Hill": 9,
            "Golden Gate Park": 22,
            "Alamo Square": 15,
            "Presidio": 24,
            "Chinatown": 7,
            "Pacific Heights": 15
        },
        "Alamo Square": {
            "Bayview": 16,
            "North Beach": 15,
            "Fisherman's Wharf": 19,
            "Haight-Ashbury": 5,
            "Nob Hill": 11,
            "Golden Gate Park": 9,
            "Union Square": 14,
            "Presidio": 17,
            "Chinatown": 15,
            "Pacific Heights": 10
        },
        "Presidio": {
            "Bayview": 31,
            "North Beach": 18,
            "Fisherman's Wharf": 19,
            "Haight-Ashbury": 15,
            "Nob Hill": 18,
            "Golden Gate Park": 12,
            "Union Square": 22,
            "Alamo Square": 19,
            "Chinatown": 21,
            "Pacific Heights": 11
        },
        "Chinatown": {
            "Bayview": 20,
            "North Beach": 3,
            "Fisherman's Wharf": 8,
            "Haight-Ashbury": 19,
            "Nob Hill": 9,
            "Golden Gate Park": 23,
            "Union Square": 7,
            "Alamo Square": 17,
            "Presidio": 19,
            "Pacific Heights": 10
        },
        "Pacific Heights": {
            "Bayview": 22,
            "North Beach": 9,
            "Fisherman's Wharf": 13,
            "Haight-Ashbury": 11,
            "Nob Hill": 8,
            "Golden Gate Park": 15,
            "Union Square": 12,
            "Alamo Square": 10,
            "Presidio": 11,
            "Chinatown": 11
        }
    }

    n_locations = len(location_names)
    travel_matrix = [[0] * n_locations for _ in range(n_locations)]
    for i, loc_i in enumerate(location_names):
        for j, loc_j in enumerate(location_names):
            if loc_i == loc_j:
                travel_matrix[i][j] = 0
            else:
                travel_matrix[i][j] = travel_dict[loc_i][loc_j]

    friends = [
        {'name': 'Brian', 'location': 'North Beach', 'duration': 90,
         'available_start': time_to_minutes("1:00PM"), 'available_end': time_to_minutes("7:00PM")},
        {'name': 'Richard', 'location': 'Fisherman\'s Wharf', 'duration': 60,
         'available_start': time_to_minutes("11:00AM"), 'available_end': time_to_minutes("12:45PM")},
        {'name': 'Ashley', 'location': 'Haight-Ashbury', 'duration': 90,
         'available_start': time_to_minutes("3:00PM"), 'available_end': time_to_minutes("8:30PM")},
        {'name': 'Elizabeth', 'location': 'Nob Hill', 'duration': 75,
         'available_start': time_to_minutes("11:45AM"), 'available_end': time_to_minutes("6:30PM")},
        {'name': 'Jessica', 'location': 'Golden Gate Park', 'duration': 105,
         'available_start': time_to_minutes("8:00PM"), 'available_end': time_to_minutes("9:45PM")},
        {'name': 'Deborah', 'location': 'Union Square', 'duration': 60,
         'available_start': time_to_minutes("5:30PM"), 'available_end': time_to_minutes("10:00PM")},
        {'name': 'Kimberly', 'location': 'Alamo Square', 'duration': 45,
         'available_start': time_to_minutes("5:30PM"), 'available_end': time_to_minutes("9:15PM")},
        {'name': 'Matthew', 'location': 'Presidio', 'duration': 15,
         'available_start': time_to_minutes("8:15AM"), 'available_end': time_to_minutes("9:00AM")},
        {'name': 'Kenneth', 'location': 'Chinatown', 'duration': 105,
         'available_start': time_to_minutes("1:45PM"), 'available_end': time_to_minutes("7:30PM")},
        {'name': 'Anthony', 'location': 'Pacific Heights', 'duration': 30,
         'available_start': time_to_minutes("2:15PM"), 'available_end': time_to_minutes("4:00PM")}
    ]

    n = len(friends)
    friend_loc_index = []
    for friend in friends:
        loc = friend['location']
        friend_loc_index.append(location_names.index(loc))

    start_time = time_to_minutes("9:00AM")
    dp = [[10**9] * n for _ in range(1<<n)]
    parent = [[None] * n for _ in range(1<<n)]

    for j in range(n):
        loc_j = friend_loc_index[j]
        travel_time_val = travel_matrix[0][loc_j]
        arrival = start_time + travel_time_val
        available_start = friends[j]['available_start']
        available_end = friends[j]['available_end']
        duration = friends[j]['duration']
        meeting_start = max(arrival, available_start)
        meeting_end = meeting_start + duration
        if meeting_end <= available_end:
            mask = 1 << j
            dp[mask][j] = meeting_end
            parent[mask][j] = (0, -1, meeting_start, meeting_end)

    for mask in range(1<<n):
        for j in range(n):
            if dp[mask][j] == 10**9:
                continue
            for k in range(n):
                if mask & (1 << k):
                    continue
                loc_j = friend_loc_index[j]
                loc_k = friend_loc_index[k]
                travel_time_val = travel_matrix[loc_j][loc_k]
                arrival = dp[mask][j] + travel_time_val
                available_start = friends[k]['available_start']
                available_end = friends[k]['available_end']
                duration = friends[k]['duration']
                meeting_start = max(arrival, available_start)
                meeting_end = meeting_start + duration
                if meeting_end <= available_end:
                    new_mask = mask | (1 << k)
                    if meeting_end < dp[new_mask][k]:
                        dp[new_mask][k] = meeting_end
                        parent[new_mask][k] = (mask, j, meeting_start, meeting_end)

    best_mask = 0
    best_j = -1
    best_count = -1
    best_end = 10**9
    for mask in range(1<<n):
        for j in range(n):
            if dp[mask][j] < 10**9:
                count = bin(mask).count("1")
                if count > best_count or (count == best_count and dp[mask][j] < best_end):
                    best_count = count
                    best_end = dp[mask][j]
                    best_mask = mask
                    best_j = j

    itinerary = []
    if best_j != -1:
        chain = []
        current_mask = best_mask
        current_j = best_j
        while current_mask != 0:
            prev_mask, prev_j, start, end = parent[current_mask][current_j]
            chain.append((current_j, start, end))
            current_mask = prev_mask
            current_j = prev_j
        chain.reverse()
        for j, start, end in chain:
            friend = friends[j]
            itinerary.append({
                "action": "meet",
                "location": friend['location'],
                "person": friend['name'],
                "start_time": minutes_to_time(start),
                "end_time": minutes_to_time(end)
            })

    result = {"itinerary": itinerary}
    print(json.dumps(result))

if __name__ == "__main__":
    main()