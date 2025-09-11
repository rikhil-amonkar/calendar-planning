import json

def main():
    # Define travel_time_dict with all given travel times
    travel_time_dict = {
        ('Haight-Ashbury', 'Mission District'): 11,
        ('Haight-Ashbury', 'Union Square'): 19,
        ('Haight-Ashbury', 'Pacific Heights'): 12,
        ('Haight-Ashbury', 'Bayview'): 18,
        ('Haight-Ashbury', 'Fisherman\'s Wharf'): 23,
        ('Haight-Ashbury', 'Marina District'): 17,
        ('Haight-Ashbury', 'Richmond District'): 10,
        ('Haight-Ashbury', 'Sunset District'): 15,
        ('Haight-Ashbury', 'Golden Gate Park'): 7,
        ('Mission District', 'Haight-Ashbury'): 12,
        ('Mission District', 'Union Square'): 15,
        ('Mission District', 'Pacific Heights'): 16,
        ('Mission District', 'Bayview'): 14,
        ('Mission District', 'Fisherman\'s Wharf'): 22,
        ('Mission District', 'Marina District'): 19,
        ('Mission District', 'Richmond District'): 20,
        ('Mission District', 'Sunset District'): 24,
        ('Mission District', 'Golden Gate Park'): 17,
        ('Union Square', 'Haight-Ashbury'): 18,
        ('Union Square', 'Mission District'): 14,
        ('Union Square', 'Pacific Heights'): 15,
        ('Union Square', 'Bayview'): 15,
        ('Union Square', 'Fisherman\'s Wharf'): 15,
        ('Union Square', 'Marina District'): 18,
        ('Union Square', 'Richmond District'): 20,
        ('Union Square', 'Sunset District'): 27,
        ('Union Square', 'Golden Gate Park'): 22,
        ('Pacific Heights', 'Haight-Ashbury'): 11,
        ('Pacific Heights', 'Mission District'): 15,
        ('Pacific Heights', 'Union Square'): 12,
        ('Pacific Heights', 'Bayview'): 22,
        ('Pacific Heights', 'Fisherman\'s Wharf'): 13,
        ('Pacific Heights', 'Marina District'): 6,
        ('Pacific Heights', 'Richmond District'): 12,
        ('Pacific Heights', 'Sunset District'): 21,
        ('Pacific Heights', 'Golden Gate Park'): 15,
        ('Bayview', 'Haight-Ashbury'): 19,
        ('Bayview', 'Mission District'): 13,
        ('Bayview', 'Union Square'): 18,
        ('Bayview', 'Pacific Heights'): 23,
        ('Bayview', 'Fisherman\'s Wharf'): 25,
        ('Bayview', 'Marina District'): 27,
        ('Bayview', 'Richmond District'): 25,
        ('Bayview', 'Sunset District'): 23,
        ('Bayview', 'Golden Gate Park'): 22,
        ('Fisherman\'s Wharf', 'Haight-Ashbury'): 22,
        ('Fisherman\'s Wharf', 'Mission District'): 22,
        ('Fisherman\'s Wharf', 'Union Square'): 13,
        ('Fisherman\'s Wharf', 'Pacific Heights'): 12,
        ('Fisherman\'s Wharf', 'Bayview'): 26,
        ('Fisherman\'s Wharf', 'Marina District'): 9,
        ('Fisherman\'s Wharf', 'Richmond District'): 18,
        ('Fisherman\'s Wharf', 'Sunset District'): 27,
        ('Fisherman\'s Wharf', 'Golden Gate Park'): 25,
        ('Marina District', 'Haight-Ashbury'): 16,
        ('Marina District', 'Mission District'): 20,
        ('Marina District', 'Union Square'): 16,
        ('Marina District', 'Pacific Heights'): 7,
        ('Marina District', 'Bayview'): 27,
        ('Marina District', 'Fisherman\'s Wharf'): 10,
        ('Marina District', 'Richmond District'): 11,
        ('Marina District', 'Sunset District'): 19,
        ('Marina District', 'Golden Gate Park'): 18,
        ('Richmond District', 'Haight-Ashbury'): 10,
        ('Richmond District', 'Mission District'): 20,
        ('Richmond District', 'Union Square'): 21,
        ('Richmond District', 'Pacific Heights'): 10,
        ('Richmond District', 'Bayview'): 27,
        ('Richmond District', 'Fisherman\'s Wharf'): 18,
        ('Richmond District', 'Marina District'): 9,
        ('Richmond District', 'Sunset District'): 11,
        ('Richmond District', 'Golden Gate Park'): 9,
        ('Sunset District', 'Haight-Ashbury'): 15,
        ('Sunset District', 'Mission District'): 25,
        ('Sunset District', 'Union Square'): 30,
        ('Sunset District', 'Pacific Heights'): 21,
        ('Sunset District', 'Bayview'): 22,
        ('Sunset District', 'Fisherman\'s Wharf'): 29,
        ('Sunset District', 'Marina District'): 21,
        ('Sunset District', 'Richmond District'): 12,
        ('Sunset District', 'Golden Gate Park'): 11,
        ('Golden Gate Park', 'Haight-Ashbury'): 7,
        ('Golden Gate Park', 'Mission District'): 17,
        ('Golden Gate Park', 'Union Square'): 22,
        ('Golden Gate Park', 'Pacific Heights'): 16,
        ('Golden Gate Park', 'Bayview'): 23,
        ('Golden Gate Park', 'Fisherman\'s Wharf'): 24,
        ('Golden Gate Park', 'Marina District'): 16,
        ('Golden Gate Park', 'Richmond District'): 7,
        ('Golden Gate Park', 'Sunset District'): 10
    }

    # Define friends with their constraints (times in minutes from midnight)
    friends_list = [
        {'name': 'Elizabeth', 'location': 'Mission District', 'start_avail': 630, 'end_avail': 1200, 'min_duration': 90},
        {'name': 'David', 'location': 'Union Square', 'start_avail': 915, 'end_avail': 1140, 'min_duration': 45},
        {'name': 'Sandra', 'location': 'Pacific Heights', 'start_avail': 420, 'end_avail': 1200, 'min_duration': 120},
        {'name': 'Thomas', 'location': 'Bayview', 'start_avail': 1170, 'end_avail': 1230, 'min_duration': 30},
        {'name': 'Robert', 'location': 'Fisherman\'s Wharf', 'start_avail': 600, 'end_avail': 900, 'min_duration': 15},
        {'name': 'Kenneth', 'location': 'Marina District', 'start_avail': 645, 'end_avail': 780, 'min_duration': 45},
        {'name': 'Melissa', 'location': 'Richmond District', 'start_avail': 1095, 'end_avail': 1200, 'min_duration': 15},
        {'name': 'Kimberly', 'location': 'Sunset District', 'start_avail': 615, 'end_avail': 1095, 'min_duration': 105},
        {'name': 'Amanda', 'location': 'Golden Gate Park', 'start_avail': 465, 'end_avail': 1125, 'min_duration': 15}
    ]

    # Define locations list and mapping to index
    locations_list = [
        'Haight-Ashbury',
        'Mission District',
        'Union Square',
        'Pacific Heights',
        'Bayview',
        'Fisherman\'s Wharf',
        'Marina District',
        'Richmond District',
        'Sunset District',
        'Golden Gate Park'
    ]
    location_to_index = {loc: idx for idx, loc in enumerate(locations_list)}

    # Build travel_matrix (10x10)
    n_locations = len(locations_list)
    travel_matrix = [[0] * n_locations for _ in range(n_locations)]
    for i in range(n_locations):
        for j in range(n_locations):
            if i == j:
                travel_matrix[i][j] = 0
            else:
                key = (locations_list[i], locations_list[j])
                if key in travel_time_dict:
                    travel_matrix[i][j] = travel_time_dict[key]
                else:
                    # Try reverse key
                    key_rev = (locations_list[j], locations_list[i])
                    travel_matrix[i][j] = travel_time_dict.get(key_rev, 1000)

    # Initialize DP and predecessor arrays
    n_friends = len(friends_list)
    dp = [[10**9] * n_locations for _ in range(1 << n_friends)]
    predecessor = [[None] * n_locations for _ in range(1 << n_friends)]
    dp[0][0] = 540  # start at Haight-Ashbury (index0) at 9:00 (540 minutes)

    # DP iteration
    for mask in range(1 << n_friends):
        for loc_idx in range(n_locations):
            if dp[mask][loc_idx] == 10**9:
                continue
            for f_idx in range(n_friends):
                if mask & (1 << f_idx):
                    continue
                friend = friends_list[f_idx]
                to_loc = friend['location']
                to_idx = location_to_index[to_loc]
                travel_time = travel_matrix[loc_idx][to_idx]
                arrival_time = dp[mask][loc_idx] + travel_time
                s = friend['start_avail']
                e = friend['end_avail']
                d = friend['min_duration']
                start_meeting = max(arrival_time, s)
                if start_meeting + d <= e:
                    end_meeting = start_meeting + d
                    new_mask = mask | (1 << f_idx)
                    if end_meeting < dp[new_mask][to_idx]:
                        dp[new_mask][to_idx] = end_meeting
                        predecessor[new_mask][to_idx] = (mask, loc_idx, f_idx, start_meeting, end_meeting)

    # Find the best mask (max number of friends, then min end time)
    best_mask = 0
    best_end_time = 10**9
    best_loc = 0
    max_friends = 0
    for mask in range(1 << n_friends):
        for loc_idx in range(n_locations):
            if dp[mask][loc_idx] < 10**9:
                count = bin(mask).count('1')
                if count > max_friends:
                    max_friends = count
                    best_mask = mask
                    best_loc = loc_idx
                    best_end_time = dp[mask][loc_idx]
                elif count == max_friends and dp[mask][loc_idx] < best_end_time:
                    best_mask = mask
                    best_loc = loc_idx
                    best_end_time = dp[mask][loc_idx]

    # Reconstruct the schedule
    itinerary = []
    mask = best_mask
    loc_idx = best_loc
    while mask != 0:
        prev_mask, prev_loc, f_idx, start_meeting, end_meeting = predecessor[mask][loc_idx]
        friend = friends_list[f_idx]
        # Convert times to string
        start_str = f"{start_meeting // 60}:{start_meeting % 60:02d}"
        end_str = f"{end_meeting // 60}:{end_meeting % 60:02d}"
        itinerary.append({
            'action': 'meet',
            'location': friend['location'],
            'person': friend['name'],
            'start_time': start_str,
            'end_time': end_str
        })
        mask = prev_mask
        loc_idx = prev_loc
    itinerary.reverse()

    # Output as JSON
    result = {'itinerary': itinerary}
    print(json.dumps(result, indent=2))

if __name__ == '__main__':
    main()