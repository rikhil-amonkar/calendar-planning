import json

def main():
    # Convert time string to minutes
    def time_to_minutes(time_str):
        parts = time_str.split(':')
        hour = int(parts[0])
        minute = int(parts[1])
        return hour * 60 + minute

    # Format minutes back to time string
    def format_time(minutes):
        hours = minutes // 60
        mins = minutes % 60
        return f"{hours}:{mins:02d}"

    # Define friends with their constraints (converted to minutes)
    friends = [
        (0, "Karen", "Haight-Ashbury", time_to_minutes("21:00"), time_to_minutes("21:45"), 45),
        (1, "Jessica", "Nob Hill", time_to_minutes("13:45"), time_to_minutes("21:00"), 90),
        (2, "Brian", "Russian Hill", time_to_minutes("15:30"), time_to_minutes("21:45"), 60),
        (3, "Kenneth", "North Beach", time_to_minutes("9:45"), time_to_minutes("21:00"), 30),
        (4, "Jason", "Chinatown", time_to_minutes("8:15"), time_to_minutes("11:45"), 75),
        (5, "Stephanie", "Union Square", time_to_minutes("14:45"), time_to_minutes("18:45"), 105),
        (6, "Kimberly", "Embarcadero", time_to_minutes("9:45"), time_to_minutes("19:30"), 75),
        (7, "Steven", "Financial District", time_to_minutes("7:15"), time_to_minutes("21:15"), 60),
        (8, "Mark", "Marina District", time_to_minutes("10:15"), time_to_minutes("13:00"), 75)
    ]
    n = len(friends)  # 9 friends

    # Travel times dictionary
    travel_times = {
        "Presidio": {
            "Haight-Ashbury": 15, "Nob Hill": 18, "Russian Hill": 14, "North Beach": 18,
            "Chinatown": 21, "Union Square": 22, "Embarcadero": 20, "Financial District": 23, "Marina District": 11
        },
        "Haight-Ashbury": {
            "Presidio": 15, "Nob Hill": 15, "Russian Hill": 17, "North Beach": 19,
            "Chinatown": 19, "Union Square": 19, "Embarcadero": 20, "Financial District": 21, "Marina District": 17
        },
        "Nob Hill": {
            "Presidio": 17, "Haight-Ashbury": 13, "Russian Hill": 5, "North Beach": 8,
            "Chinatown": 6, "Union Square": 7, "Embarcadero": 9, "Financial District": 9, "Marina District": 11
        },
        "Russian Hill": {
            "Presidio": 14, "Haight-Ashbury": 17, "Nob Hill": 5, "North Beach": 5,
            "Chinatown": 9, "Union Square": 10, "Embarcadero": 8, "Financial District": 11, "Marina District": 7
        },
        "North Beach": {
            "Presidio": 17, "Haight-Ashbury": 18, "Nob Hill": 7, "Russian Hill": 4,
            "Chinatown": 6, "Union Square": 7, "Embarcadero": 6, "Financial District": 8, "Marina District": 9
        },
        "Chinatown": {
            "Presidio": 19, "Haight-Ashbury": 19, "Nob Hill": 9, "Russian Hill": 7,
            "North Beach": 3, "Union Square": 7, "Embarcadero": 5, "Financial District": 5, "Marina District": 12
        },
        "Union Square": {
            "Presidio": 24, "Haight-Ashbury": 18, "Nob Hill": 9, "Russian Hill": 13,
            "North Beach": 10, "Chinatown": 7, "Embarcadero": 11, "Financial District": 9, "Marina District": 18
        },
        "Embarcadero": {
            "Presidio": 20, "Haight-Ashbury": 21, "Nob Hill": 10, "Russian Hill": 8,
            "North Beach": 5, "Chinatown": 7, "Union Square": 10, "Financial District": 5, "Marina District": 12
        },
        "Financial District": {
            "Presidio": 22, "Haight-Ashbury": 19, "Nob Hill": 8, "Russian Hill": 11,
            "North Beach": 7, "Chinatown": 5, "Union Square": 9, "Embarcadero": 4, "Marina District": 15
        },
        "Marina District": {
            "Presidio": 10, "Haight-Ashbury": 16, "Nob Hill": 12, "Russian Hill": 8,
            "North Beach": 11, "Chinatown": 15, "Union Square": 16, "Embarcadero": 14, "Financial District": 17
        }
    }
    
    # Get all unique locations
    all_locations = list(travel_times.keys())
    loc_to_index = {loc: idx for idx, loc in enumerate(all_locations)}
    n_loc = len(all_locations)
    
    # Initialize DP and parent arrays
    dp = [[float('inf')] * n_loc for _ in range(1 << n)]
    parent = [[None] * n_loc for _ in range(1 << n)]  # (prev_bitmask, prev_loc_idx, friend_index, start_time, end_time)
    
    # Start at Presidio at 9:00 (540 minutes)
    start_loc = "Presidio"
    start_idx = loc_to_index[start_loc]
    dp[0][start_idx] = 540  # 9:00 in minutes
    
    # Iterate over all states
    for bitmask in range(1 << n):
        for loc_idx in range(n_loc):
            current_time = dp[bitmask][loc_idx]
            if current_time == float('inf'):
                continue
            current_loc = all_locations[loc_idx]
            for j in range(n):
                if bitmask & (1 << j):
                    continue
                friend = friends[j]
                friend_loc = friend[2]
                # Get travel time from current_loc to friend's location
                tt = travel_times[current_loc][friend_loc]
                arrival_time = current_time + tt
                # Meeting must start at max of arrival and friend's available start
                start_meeting = max(arrival_time, friend[3])
                end_meeting = start_meeting + friend[5]
                # Check if meeting can be scheduled within friend's window
                if end_meeting > friend[4]:
                    continue
                new_bitmask = bitmask | (1 << j)
                new_loc_idx = loc_to_index[friend_loc]
                if end_meeting < dp[new_bitmask][new_loc_idx]:
                    dp[new_bitmask][new_loc_idx] = end_meeting
                    parent[new_bitmask][new_loc_idx] = (bitmask, loc_idx, j, start_meeting, end_meeting)
    
    # Find the state with the maximum number of meetings
    best_bitmask = None
    best_loc_idx = None
    best_count = -1
    best_end_time = float('inf')
    for bitmask in range(1 << n):
        count = bin(bitmask).count("1")
        for loc_idx in range(n_loc):
            if dp[bitmask][loc_idx] == float('inf'):
                continue
            if count > best_count or (count == best_count and dp[bitmask][loc_idx] < best_end_time):
                best_count = count
                best_bitmask = bitmask
                best_loc_idx = loc_idx
                best_end_time = dp[bitmask][loc_idx]
    
    # Backtrack to get the itinerary
    itinerary = []
    current_bitmask = best_bitmask
    current_loc_idx = best_loc_idx
    while current_bitmask != 0 and parent[current_bitmask][current_loc_idx] is not None:
        prev_bitmask, prev_loc_idx, j, S, E = parent[current_bitmask][current_loc_idx]
        friend = friends[j]
        itinerary.append({
            "action": "meet",
            "location": friend[2],
            "person": friend[1],
            "start_time": format_time(S),
            "end_time": format_time(E)
        })
        current_bitmask = prev_bitmask
        current_loc_idx = prev_loc_idx
    
    # Reverse to get chronological order
    itinerary.reverse()
    
    # Output as JSON
    result = {"itinerary": itinerary}
    print(json.dumps(result))

if __name__ == '__main__':
    main()