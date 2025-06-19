import json

def main():
    # Define all locations
    all_locations = [
        'Union Square',
        'Presidio',
        'Alamo Square',
        'Marina District',
        'Financial District',
        'Nob Hill',
        'Sunset District',
        'Chinatown',
        'Russian Hill',
        'North Beach',
        'Haight-Ashbury'
    ]
    
    # Map location to index for fast lookup
    location_to_index = {loc: idx for idx, loc in enumerate(all_locations)}
    
    # Build the travel_times dictionary (fixed missing Sunset District->Presidio)
    travel_times = {
        ('Union Square', 'Presidio'): 24,
        ('Union Square', 'Alamo Square'): 15,
        ('Union Square', 'Marina District'): 18,
        ('Union Square', 'Financial District'): 9,
        ('Union Square', 'Nob Hill'): 9,
        ('Union Square', 'Sunset District'): 27,
        ('Union Square', 'Chinatown'): 7,
        ('Union Square', 'Russian Hill'): 13,
        ('Union Square', 'North Beach'): 10,
        ('Union Square', 'Haight-Ashbury'): 18,
        ('Presidio', 'Union Square'): 22,
        ('Presidio', 'Alamo Square'): 19,
        ('Presidio', 'Marina District'): 11,
        ('Presidio', 'Financial District'): 23,
        ('Presidio', 'Nob Hill'): 18,
        ('Presidio', 'Sunset District'): 15,
        ('Presidio', 'Chinatown'): 21,
        ('Presidio', 'Russian Hill'): 14,
        ('Presidio', 'North Beach'): 18,
        ('Presidio', 'Haight-Ashbury'): 15,
        ('Alamo Square', 'Union Square'): 14,
        ('Alamo Square', 'Presidio'): 17,
        ('Alamo Square', 'Marina District'): 15,
        ('Alamo Square', 'Financial District'): 17,
        ('Alamo Square', 'Nob Hill'): 11,
        ('Alamo Square', 'Sunset District'): 16,
        ('Alamo Square', 'Chinatown'): 15,
        ('Alamo Square', 'Russian Hill'): 13,
        ('Alamo Square', 'North Beach'): 15,
        ('Alamo Square', 'Haight-Ashbury'): 5,
        ('Marina District', 'Union Square'): 16,
        ('Marina District', 'Presidio'): 10,
        ('Marina District', 'Alamo Square'): 15,
        ('Marina District', 'Financial District'): 17,
        ('Marina District', 'Nob Hill'): 12,
        ('Marina District', 'Sunset District'): 19,
        ('Marina District', 'Chinatown'): 15,
        ('Marina District', 'Russian Hill'): 8,
        ('Marina District', 'North Beach'): 11,
        ('Marina District', 'Haight-Ashbury'): 16,
        ('Financial District', 'Union Square'): 9,
        ('Financial District', 'Presidio'): 22,
        ('Financial District', 'Alamo Square'): 17,
        ('Financial District', 'Marina District'): 15,
        ('Financial District', 'Nob Hill'): 8,
        ('Financial District', 'Sunset District'): 30,
        ('Financial District', 'Chinatown'): 5,
        ('Financial District', 'Russian Hill'): 11,
        ('Financial District', 'North Beach'): 7,
        ('Financial District', 'Haight-Ashbury'): 19,
        ('Nob Hill', 'Union Square'): 7,
        ('Nob Hill', 'Presidio'): 17,
        ('Nob Hill', 'Alamo Square'): 11,
        ('Nob Hill', 'Marina District'): 11,
        ('Nob Hill', 'Financial District'): 9,
        ('Nob Hill', 'Sunset District'): 24,
        ('Nob Hill', 'Chinatown'): 6,
        ('Nob Hill', 'Russian Hill'): 5,
        ('Nob Hill', 'North Beach'): 8,
        ('Nob Hill', 'Haight-Ashbury'): 13,
        ('Sunset District', 'Union Square'): 30,
        ('Sunset District', 'Presidio'): 15,  # Added missing entry
        ('Sunset District', 'Alamo Square'): 17,
        ('Sunset District', 'Marina District'): 21,
        ('Sunset District', 'Financial District'): 30,
        ('Sunset District', 'Nob Hill'): 27,
        ('Sunset District', 'Chinatown'): 30,
        ('Sunset District', 'Russian Hill'): 24,
        ('Sunset District', 'North Beach'): 28,
        ('Sunset District', 'Haight-Ashbury'): 15,
        ('Chinatown', 'Union Square'): 7,
        ('Chinatown', 'Presidio'): 19,
        ('Chinatown', 'Alamo Square'): 17,
        ('Chinatown', 'Marina District'): 12,
        ('Chinatown', 'Financial District'): 5,
        ('Chinatown', 'Nob Hill'): 9,
        ('Chinatown', 'Sunset District'): 29,
        ('Chinatown', 'Russian Hill'): 7,
        ('Chinatown', 'North Beach'): 3,
        ('Chinatown', 'Haight-Ashbury'): 19,
        ('Russian Hill', 'Union Square'): 10,
        ('Russian Hill', 'Presidio'): 14,
        ('Russian Hill', 'Alamo Square'): 15,
        ('Russian Hill', 'Marina District'): 7,
        ('Russian Hill', 'Financial District'): 11,
        ('Russian Hill', 'Nob Hill'): 5,
        ('Russian Hill', 'Sunset District'): 23,
        ('Russian Hill', 'Chinatown'): 9,
        ('Russian Hill', 'North Beach'): 5,
        ('Russian Hill', 'Haight-Ashbury'): 17,
        ('North Beach', 'Union Square'): 7,
        ('North Beach', 'Presidio'): 17,
        ('North Beach', 'Alamo Square'): 16,
        ('North Beach', 'Marina District'): 9,
        ('North Beach', 'Financial District'): 8,
        ('North Beach', 'Nob Hill'): 7,
        ('North Beach', 'Sunset District'): 27,
        ('North Beach', 'Chinatown'): 6,
        ('North Beach', 'Russian Hill'): 4,
        ('North Beach', 'Haight-Ashbury'): 18,
        ('Haight-Ashbury', 'Union Square'): 19,
        ('Haight-Ashbury', 'Presidio'): 15,
        ('Haight-Ashbury', 'Alamo Square'): 5,
        ('Haight-Ashbury', 'Marina District'): 17,
        ('Haight-Ashbury', 'Financial District'): 21,
        ('Haight-Ashbury', 'Nob Hill'): 15,
        ('Haight-Ashbury', 'Sunset District'): 15,
        ('Haight-Ashbury', 'Chinatown'): 19,
        ('Haight-Ashbury', 'Russian Hill'): 17,
        ('Haight-Ashbury', 'North Beach'): 19
    }
    
    # Define friends with their constraints (times in minutes from midnight)
    friends = [
        {'name': 'Kimberly', 'location': 'Presidio', 'start': 15*60+30, 'end': 16*60, 'min_duration': 15},
        {'name': 'Elizabeth', 'location': 'Alamo Square', 'start': 19*60+15, 'end': 20*60+15, 'min_duration': 15},
        {'name': 'Joshua', 'location': 'Marina District', 'start': 10*60+30, 'end': 14*60+15, 'min_duration': 45},
        {'name': 'Sandra', 'location': 'Financial District', 'start': 19*60+30, 'end': 20*60+15, 'min_duration': 45},
        {'name': 'Kenneth', 'location': 'Nob Hill', 'start': 12*60+45, 'end': 21*60+45, 'min_duration': 30},
        {'name': 'Betty', 'location': 'Sunset District', 'start': 14*60, 'end': 19*60, 'min_duration': 60},
        {'name': 'Deborah', 'location': 'Chinatown', 'start': 17*60+15, 'end': 20*60+30, 'min_duration': 15},
        {'name': 'Barbara', 'location': 'Russian Hill', 'start': 17*60+30, 'end': 21*60+15, 'min_duration': 120},
        {'name': 'Steven', 'location': 'North Beach', 'start': 17*60+45, 'end': 20*60+45, 'min_duration': 90},
        {'name': 'Daniel', 'location': 'Haight-Ashbury', 'start': 18*60+30, 'end': 18*60+45, 'min_duration': 15}
    ]
    
    n = len(friends)  # 10 friends
    num_masks = 1 << n
    num_locations = len(all_locations)
    INF = 10**9
    
    # dp[mask][loc_index] = minimal end time (time we finish meeting and are free to leave) at location with index loc_index, having scheduled friends in mask
    dp = [[INF] * num_locations for _ in range(num_masks)]
    # parent: (prev_mask, prev_loc_index, friend_index, start_time, end_time) for state (mask, loc_index)
    parent = [[None] * num_locations for _ in range(num_masks)]
    
    # Initialize: start at Union Square at 9:00 (540 minutes)
    start_loc_index = location_to_index['Union Square']
    dp[0][start_loc_index] = 540  # 9:00 AM in minutes
    
    # Iterate over masks
    for mask in range(num_masks):
        for loc_idx in range(num_locations):
            if dp[mask][loc_idx] == INF:
                continue
            current_time = dp[mask][loc_idx]
            current_loc = all_locations[loc_idx]
            # Try to schedule each unscheduled friend
            for j, friend in enumerate(friends):
                if mask & (1 << j):
                    continue
                # Get travel time from current_loc to friend's location
                to_loc = friend['location']
                key = (current_loc, to_loc)
                if key not in travel_times:
                    # Skip if no travel time (shouldn't happen with complete dictionary)
                    continue
                travel = travel_times[key]
                # Calculate arrival time at friend's location
                arrival_time = current_time + travel
                # The meeting can start at the later of arrival_time and friend's start time
                start_time = max(arrival_time, friend['start'])
                # Check if we can meet for the minimum duration
                if start_time + friend['min_duration'] <= friend['end']:
                    end_time = start_time + friend['min_duration']
                    new_mask = mask | (1 << j)
                    new_loc_idx = location_to_index[to_loc]
                    # Update if we found a smaller end time for the new state
                    if end_time < dp[new_mask][new_loc_idx]:
                        dp[new_mask][new_loc_idx] = end_time
                        parent[new_mask][new_loc_idx] = (mask, loc_idx, j, start_time, end_time)
    
    # Find the best state: maximum number of meetings, and if tie minimal end time
    best_mask = 0
    best_count = 0
    best_end_time = INF
    best_loc_idx = -1
    for mask in range(num_masks):
        for loc_idx in range(num_locations):
            if dp[mask][loc_idx] < INF:
                count = bin(mask).count("1")
                if count > best_count or (count == best_count and dp[mask][loc_idx] < best_end_time):
                    best_count = count
                    best_end_time = dp[mask][loc_idx]
                    best_mask = mask
                    best_loc_idx = loc_idx
    
    # Reconstruct the itinerary
    itinerary = []
    current_mask = best_mask
    current_loc_idx = best_loc_idx
    # Backtrack to get meetings in reverse order
    while current_mask != 0:
        if parent[current_mask][current_loc_idx] is None:
            break
        prev_mask, prev_loc_idx, j, start_time, end_time = parent[current_mask][current_loc_idx]
        friend_j = friends[j]
        # Convert times to string
        def format_time(minutes):
            h = minutes // 60
            m = minutes % 60
            return f"{h}:{m:02d}"
        meeting = {
            'action': 'meet',
            'location': friend_j['location'],
            'person': friend_j['name'],
            'start_time': format_time(start_time),
            'end_time': format_time(end_time)
        }
        itinerary.append(meeting)
        current_mask = prev_mask
        current_loc_idx = prev_loc_idx
    
    # Reverse to get chronological order
    itinerary.reverse()
    
    # Output as JSON
    result = {
        "itinerary": itinerary
    }
    print(json.dumps(result))

if __name__ == "__main__":
    main()