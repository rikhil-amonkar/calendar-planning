import json

def main():
    # Convert time string to minutes
    def time_to_min(time_str):
        parts = time_str.split(':')
        hour = int(parts[0])
        minute = int(parts[1]) if len(parts) > 1 else 0
        return hour * 60 + minute

    # Convert minutes to time string
    def min_to_time(minutes):
        hour = minutes // 60
        minute = minutes % 60
        return f"{hour}:{minute:02d}"

    # Location to index mapping
    locations = [
        "Union Square",
        "Russian Hill",
        "Alamo Square",
        "Haight-Ashbury",
        "Marina District",
        "Bayview",
        "Chinatown",
        "Presidio",
        "Sunset District"
    ]
    loc_to_idx = {loc: idx for idx, loc in enumerate(locations)}
    
    # Build travel matrix (9x9)
    travel_matrix = [[0] * 9 for _ in range(9)]
    
    # Assign travel times
    travel_matrix[0][1] = 13
    travel_matrix[0][2] = 15
    travel_matrix[0][3] = 18
    travel_matrix[0][4] = 18
    travel_matrix[0][5] = 15
    travel_matrix[0][6] = 7
    travel_matrix[0][7] = 24
    travel_matrix[0][8] = 27
    
    travel_matrix[1][0] = 10
    travel_matrix[1][2] = 15
    travel_matrix[1][3] = 17
    travel_matrix[1][4] = 7
    travel_matrix[1][5] = 23
    travel_matrix[1][6] = 9
    travel_matrix[1][7] = 14
    travel_matrix[1][8] = 23
    
    travel_matrix[2][0] = 14
    travel_matrix[2][1] = 13
    travel_matrix[2][3] = 5
    travel_matrix[2][4] = 15
    travel_matrix[2][5] = 16
    travel_matrix[2][6] = 15
    travel_matrix[2][7] = 17
    travel_matrix[2][8] = 16
    
    travel_matrix[3][0] = 19
    travel_matrix[3][1] = 17
    travel_matrix[3][2] = 5
    travel_matrix[3][4] = 17
    travel_matrix[3][5] = 18
    travel_matrix[3][6] = 19
    travel_matrix[3][7] = 15
    travel_matrix[3][8] = 15
    
    travel_matrix[4][0] = 16
    travel_matrix[4][1] = 8
    travel_matrix[4][2] = 15
    travel_matrix[4][3] = 16
    travel_matrix[4][5] = 27
    travel_matrix[4][6] = 15
    travel_matrix[4][7] = 10
    travel_matrix[4][8] = 19
    
    travel_matrix[5][0] = 18
    travel_matrix[5][1] = 23
    travel_matrix[5][2] = 16
    travel_matrix[5][3] = 19
    travel_matrix[5][4] = 27
    travel_matrix[5][6] = 19
    travel_matrix[5][7] = 32
    travel_matrix[5][8] = 23
    
    travel_matrix[6][0] = 7
    travel_matrix[6][1] = 7
    travel_matrix[6][2] = 17
    travel_matrix[6][3] = 19
    travel_matrix[6][4] = 12
    travel_matrix[6][5] = 20
    travel_matrix[6][7] = 19
    travel_matrix[6][8] = 29
    
    travel_matrix[7][0] = 22
    travel_matrix[7][1] = 14
    travel_matrix[7][2] = 19
    travel_matrix[7][3] = 15
    travel_matrix[7][4] = 11
    travel_matrix[7][5] = 31
    travel_matrix[7][6] = 21
    travel_matrix[7][8] = 15
    
    travel_matrix[8][0] = 30
    travel_matrix[8][1] = 24
    travel_matrix[8][2] = 17
    travel_matrix[8][3] = 15
    travel_matrix[8][4] = 21
    travel_matrix[8][5] = 22
    travel_matrix[8][6] = 30
    travel_matrix[8][7] = 16

    # Friends data
    friends = [
        {'name': 'Betty', 'location': 'Russian Hill', 'start': time_to_min('7:00'), 'end': time_to_min('16:45'), 'duration': 105, 'loc_idx': loc_to_idx['Russian Hill']},
        {'name': 'Melissa', 'location': 'Alamo Square', 'start': time_to_min('9:30'), 'end': time_to_min('17:15'), 'duration': 105, 'loc_idx': loc_to_idx['Alamo Square']},
        {'name': 'Joshua', 'location': 'Haight-Ashbury', 'start': time_to_min('12:15'), 'end': time_to_min('19:00'), 'duration': 90, 'loc_idx': loc_to_idx['Haight-Ashbury']},
        {'name': 'Jeffrey', 'location': 'Marina District', 'start': time_to_min('12:15'), 'end': time_to_min('18:00'), 'duration': 45, 'loc_idx': loc_to_idx['Marina District']},
        {'name': 'James', 'location': 'Bayview', 'start': time_to_min('7:30'), 'end': time_to_min('20:00'), 'duration': 90, 'loc_idx': loc_to_idx['Bayview']},
        {'name': 'Anthony', 'location': 'Chinatown', 'start': time_to_min('11:45'), 'end': time_to_min('13:30'), 'duration': 75, 'loc_idx': loc_to_idx['Chinatown']},
        {'name': 'Timothy', 'location': 'Presidio', 'start': time_to_min('12:30'), 'end': time_to_min('14:45'), 'duration': 90, 'loc_idx': loc_to_idx['Presidio']},
        {'name': 'Emily', 'location': 'Sunset District', 'start': time_to_min('19:30'), 'end': time_to_min('21:30'), 'duration': 120, 'loc_idx': loc_to_idx['Sunset District']}
    ]

    n_friends = len(friends)
    n_locs = len(locations)
    INF = 10**9
    dp = [[INF] * n_locs for _ in range(1 << n_friends)]
    prev = [[None] * n_locs for _ in range(1 << n_friends)]  # (prev_mask, prev_loc, friend_idx, start_time)

    # Start at Union Square (index 0) at 9:00 (540 minutes)
    dp[0][0] = time_to_min('9:00')

    # Dynamic programming
    for mask in range(1 << n_friends):
        for loc in range(n_locs):
            if dp[mask][loc] == INF:
                continue
            for idx, friend in enumerate(friends):
                if mask & (1 << idx):
                    continue
                to_loc = friend['loc_idx']
                travel_time = travel_matrix[loc][to_loc]
                arrival = dp[mask][loc] + travel_time
                start_meet = max(arrival, friend['start'])
                end_meet = start_meet + friend['duration']
                if end_meet > friend['end']:
                    continue
                new_mask = mask | (1 << idx)
                if end_meet < dp[new_mask][to_loc]:
                    dp[new_mask][to_loc] = end_meet
                    prev[new_mask][to_loc] = (mask, loc, idx, start_meet)

    # Find best state (max meetings, then min end time)
    best_mask = 0
    best_loc = 0
    max_meetings = -1
    min_time = INF
    for mask in range(1 << n_friends):
        for loc in range(n_locs):
            if dp[mask][loc] < INF:
                count = bin(mask).count('1')
                if count > max_meetings or (count == max_meetings and dp[mask][loc] < min_time):
                    max_meetings = count
                    min_time = dp[mask][loc]
                    best_mask = mask
                    best_loc = loc

    # Reconstruct itinerary
 itinerary = []
    current_mask = best_mask
    current_loc = best_loc
    while current_mask != 0:
        prev_mask, prev_loc, friend_idx, start_time = prev[current_mask][current_loc]
        friend = friends[friend_idx]
        itinerary.append({
            'action': 'meet',
            'location': friend['location'],
            'person': friend['name'],
            'start_time': min_to_time(start_time),
            'end_time': min_to_time(start_time + friend['duration'])
        })
        current_mask = prev_mask
        current_loc = prev_loc
    itinerary.reverse()

    # Output as JSON
    result = {'itinerary': itinerary}
    print(json.dumps(result, indent=2))

if __name__ == '__main__':
    main()