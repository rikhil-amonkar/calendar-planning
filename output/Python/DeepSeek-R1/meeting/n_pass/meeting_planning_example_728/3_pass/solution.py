import json

def main():
    # Travel times dictionary
    travel_times = {
        'Marina District': {
            'Marina District': 0,
            'Mission District': 20,
            'Fisherman\'s Wharf': 10,
            'Presidio': 10,
            'Union Square': 16,
            'Sunset District': 19,
            'Financial District': 17,
            'Haight-Ashbury': 16,
            'Russian Hill': 8
        },
        'Mission District': {
            'Marina District': 19,
            'Mission District': 0,
            'Fisherman\'s Wharf': 22,
            'Presidio': 25,
            'Union Square': 15,
            'Sunset District': 24,
            'Financial District': 15,
            'Haight-Ashbury': 12,
            'Russian Hill': 15
        },
        'Fisherman\'s Wharf': {
            'Marina District': 9,
            'Mission District': 22,
            'Fisherman\'s Wharf': 0,
            'Presidio': 17,
            'Union Square': 13,
            'Sunset District': 27,
            'Financial District': 11,
            'Haight-Ashbury': 22,
            'Russian Hill': 7
        },
        'Presidio': {
            'Marina District': 11,
            'Mission District': 26,
            'Fisherman\'s Wharf': 19,
            'Presidio': 0,
            'Union Square': 22,
            'Sunset District': 15,
            'Financial District': 23,
            'Haight-Ashbury': 15,
            'Russian Hill': 14
        },
        'Union Square': {
            'Marina District': 18,
            'Mission District': 14,
            'Fisherman\'s Wharf': 15,
            'Presidio': 24,
            'Union Square': 0,
            'Sunset District': 27,
            'Financial District': 9,
            'Haight-Ashbury': 18,
            'Russian Hill': 13
        },
        'Sunset District': {
            'Marina District': 21,
            'Mission District': 25,
            'Fisherman\'s Wharf': 29,
            'Presidio': 16,
            'Union Square': 30,
            'Sunset District': 0,
            'Financial District': 30,
            'Haight-Ashbury': 15,
            'Russian Hill': 24
        },
        'Financial District': {
            'Marina District': 15,
            'Mission District': 17,
            'Fisherman\'s Wharf': 10,
            'Presidio': 22,
            'Union Square': 9,
            'Sunset District': 30,
            'Financial District': 0,
            'Haight-Ashbury': 19,
            'Russian Hill': 11
        },
        'Haight-Ashbury': {
            'Marina District': 17,
            'Mission District': 11,
            'Fisherman\'s Wharf': 23,
            'Presidio': 15,
            'Union Square': 19,
            'Sunset District': 15,
            'Financial District': 21,
            'Haight-Ashbury': 0,
            'Russian Hill': 17
        },
        'Russian Hill': {
            'Marina District': 7,
            'Mission District': 16,
            'Fisherman\'s Wharf': 7,
            'Presidio': 14,
            'Union Square': 10,
            'Sunset District': 23,
            'Financial District': 11,
            'Haight-Ashbury': 17,
            'Russian Hill': 0
        }
    }

    # Symmetrize travel times by taking max of both directions
    locations = list(travel_times.keys())
    for i in range(len(locations)):
        for j in range(i + 1, len(locations)):
            loc1 = locations[i]
            loc2 = locations[j]
            t1 = travel_times[loc1][loc2]
            t2 = travel_times[loc2][loc1]
            if t1 != t2:
                max_t = max(t1, t2)
                travel_times[loc1][loc2] = max_t
                travel_times[loc2][loc1] = max_t

    # Friends data
    friends = [
        {'name': 'Karen', 'location': 'Mission District', 'start_minutes': 14*60+15, 'end_minutes': 22*60, 'min_duration': 30},
        {'name': 'Richard', 'location': 'Fisherman\'s Wharf', 'start_minutes': 14*60+30, 'end_minutes': 17*60+30, 'min_duration': 30},
        {'name': 'Robert', 'location': 'Presidio', 'start_minutes': 21*60+45, 'end_minutes': 22*60+45, 'min_duration': 60},
        {'name': 'Joseph', 'location': 'Union Square', 'start_minutes': 11*60+45, 'end_minutes': 14*60+45, 'min_duration': 120},
        {'name': 'Helen', 'location': 'Sunset District', 'start_minutes': 14*60+45, 'end_minutes': 20*60+45, 'min_duration': 105},
        {'name': 'Elizabeth', 'location': 'Financial District', 'start_minutes': 10*60, 'end_minutes': 12*60+45, 'min_duration': 75},
        {'name': 'Kimberly', 'location': 'Haight-Ashbury', 'start_minutes': 14*60+15, 'end_minutes': 17*60+30, 'min_duration': 105},
        {'name': 'Ashley', 'location': 'Russian Hill', 'start_minutes': 11*60+30, 'end_minutes': 21*60+30, 'min_duration': 45}
    ]

    # Locations and indices
    loc_index = {loc: idx for idx, loc in enumerate(locations)}
    n = len(friends)
    num_locations = len(locations)

    # Initialize DP and parent arrays
    dp = [[10**9] * num_locations for _ in range(1 << n)]
    parent = [[None] * num_locations for _ in range(1 << n)]
    
    # Start at Marina District at 9:00 AM (540 minutes)
    start_loc_id = loc_index['Marina District']
    dp[0][start_loc_id] = 540

    # Run DP
    for mask in range(1 << n):
        for loc_id in range(num_locations):
            if dp[mask][loc_id] == 10**9:
                continue
            current_time = dp[mask][loc_id]
            current_loc = locations[loc_id]
            for j in range(n):
                if mask & (1 << j):
                    continue
                friend = friends[j]
                next_loc = friend['location']
                next_loc_id = loc_index[next_loc]
                tt = travel_times[current_loc][next_loc]
                arrival_time = current_time + tt
                start_meeting = max(arrival_time, friend['start_minutes'])
                if start_meeting + friend['min_duration'] > friend['end_minutes']:
                    continue
                end_meeting = start_meeting + friend['min_duration']
                new_mask = mask | (1 << j)
                if end_meeting < dp[new_mask][next_loc_id]:
                    dp[new_mask][next_loc_id] = end_meeting
                    parent[new_mask][next_loc_id] = (mask, loc_id, j, start_meeting, end_meeting)
    
    # Find best state with maximum meetings that can return to Marina by 23:00 (1380 minutes)
    best_count = -1
    best_mask = 0
    best_loc_id = -1
    best_time = 10**9
    for mask in range(1 << n):
        count = bin(mask).count('1')
        for loc_id in range(num_locations):
            if dp[mask][loc_id] == 10**9:
                continue
            # Calculate the time to return to Marina
            current_loc = locations[loc_id]
            travel_back = travel_times[current_loc]['Marina District']
            return_time = dp[mask][loc_id] + travel_back
            if return_time > 1380:
                continue
            if count > best_count or (count == best_count and dp[mask][loc_id] < best_time):
                best_count = count
                best_mask = mask
                best_loc_id = loc_id
                best_time = dp[mask][loc_id]
    
    # Reconstruct itinerary
    itinerary = []
    mask = best_mask
    loc_id = best_loc_id
    while mask != 0:
        if parent[mask][loc_id] is None:
            break
        prev_mask, prev_loc_id, j, start_meeting, end_meeting = parent[mask][loc_id]
        friend = friends[j]
        itinerary.insert(0, {
            'action': 'meet',
            'location': friend['location'],
            'person': friend['name'],
            'start_time': minutes_to_time_str(start_meeting),
            'end_time': minutes_to_time_str(end_meeting)
        })
        mask = prev_mask
        loc_id = prev_loc_id
    
    # Output as JSON
    result = {
        "itinerary": itinerary
    }
    print(json.dumps(result))

def minutes_to_time_str(total_minutes):
    hours = total_minutes // 60
    minutes = total_minutes % 60
    return f"{hours}:{minutes:02d}"

if __name__ == "__main__":
    main()