# SOLUTION:
import json

def main():
    # Convert time string to minutes since midnight
    def time_to_minutes(time_str):
        parts = time_str.split(':')
        hour = int(parts[0])
        minute = int(parts[1]) if len(parts) > 1 else 0
        return hour * 60 + minute

    # Format minutes since midnight to "H:MM"
    def format_time(minutes):
        h = minutes // 60
        m = minutes % 60
        return f"{h}:{m:02d}"

    # Locations: index 0 to 10
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
    
    # Friend data: name, location index, start (minutes), end (minutes), duration (minutes)
    friends = [
        {'name': 'Mary', 'location': 1, 'start': time_to_minutes("20:00"), 'end': time_to_minutes("21:15"), 'duration': 75},
        {'name': 'Kenneth', 'location': 2, 'start': time_to_minutes("11:15"), 'end': time_to_minutes("19:15"), 'duration': 30},
        {'name': 'Joseph', 'location': 3, 'start': time_to_minutes("20:00"), 'end': time_to_minutes("22:00"), 'duration': 120},
        {'name': 'Sarah', 'location': 4, 'start': time_to_minutes("11:45"), 'end': time_to_minutes("14:30"), 'duration': 90},
        {'name': 'Thomas', 'location': 5, 'start': time_to_minutes("19:15"), 'end': time_to_minutes("19:45"), 'duration': 15},
        {'name': 'Daniel', 'location': 6, 'start': time_to_minutes("13:45"), 'end': time_to_minutes("20:30"), 'duration': 15},
        {'name': 'Richard', 'location': 7, 'start': time_to_minutes("8:00"), 'end': time_to_minutes("18:45"), 'duration': 30},
        {'name': 'Mark', 'location': 8, 'start': time_to_minutes("17:30"), 'end': time_to_minutes("21:30"), 'duration': 120},
        {'name': 'David', 'location': 9, 'start': time_to_minutes("20:00"), 'end': time_to_minutes("21:00"), 'duration': 60},
        {'name': 'Karen', 'location': 10, 'start': time_to_minutes("13:15"), 'end': time_to_minutes("18:30"), 'duration': 120}
    ]
    
    # Asymmetric travel times between locations (11x11 matrix)
    travel_time = [
        [0, 9, 17, 13, 7, 8, 8, 6, 17, 11, 5],
        [10, 0, 25, 21, 10, 5, 11, 7, 25, 12, 8],
        [16, 22, 0, 6, 19, 20, 16, 22, 11, 21, 18],
        [15, 20, 6, 0, 19, 19, 12, 19, 7, 17, 17],
        [9, 11, 17, 18, 0, 10, 15, 7, 22, 18, 13],
        [7, 6, 23, 18, 7, 0, 8, 6, 22, 9, 4],
        [8, 10, 16, 11, 12, 9, 0, 11, 15, 6, 7],
        [9, 5, 22, 19, 7, 3, 10, 0, 23, 12, 7],
        [20, 25, 13, 7, 22, 23, 16, 23, 0, 16, 19],
        [12, 14, 22, 16, 16, 11, 7, 15, 18, 0, 8],
        [5, 8, 21, 17, 10, 5, 7, 9, 21, 7, 0]
    ]
    
    n_friends = len(friends)
    n_locations = len(locations)
    n_states = 1 << n_friends
    
    # Initialize DP and parent arrays
    dp = [[10**9] * n_locations for _ in range(n_states)]
    parent = [[None] * n_locations for _ in range(n_states)]  # (prev_state, prev_loc, friend_index, start, end)
    
    # Start at Nob Hill (location 0) at 9:00 AM (540 minutes)
    start_time = time_to_minutes("9:00")
    dp[0][0] = start_time
    
    # Iterate over all states
    for state in range(n_states):
        for loc in range(n_locations):
            if dp[state][loc] == 10**9:
                continue
            current_time = dp[state][loc]
            # Try to meet each unvisited friend
            for j in range(n_friends):
                if state & (1 << j):
                    continue
                friend = friends[j]
                to_loc = friend['location']
                travel_duration = travel_time[loc][to_loc]
                arrival_time = current_time + travel_duration
                # Calculate meeting start time (cannot start before friend's availability)
                meeting_start = max(arrival_time, friend['start'])
                meeting_end = meeting_start + friend['duration']
                # Check if meeting fits within friend's window
                if meeting_end <= friend['end']:
                    new_state = state | (1 << j)
                    if meeting_end < dp[new_state][to_loc]:
                        dp[new_state][to_loc] = meeting_end
                        parent[new_state][to_loc] = (state, loc, j, meeting_start, meeting_end)
    
    # Find state with maximum friends met
    best_state = 0
    best_loc = 0
    best_count = 0
    for state in range(n_states):
        count = bin(state).count("1")
        for loc in range(n_locations):
            if dp[state][loc] < 10**9:
                if count > best_count or (count == best_count and dp[state][loc] < dp[best_state][best_loc]):
                    best_count = count
                    best_state = state
                    best_loc = loc
    
    # Backtrack to build itinerary
    itinerary = []
    state = best_state
    loc = best_loc
    while state != 0:
        if parent[state][loc] is None:
            break
        prev_state, prev_loc, j, start, end = parent[state][loc]
        friend = friends[j]
        itinerary.append({
            "action": "meet",
            "location": locations[friend['location']],
            "person": friend['name'],
            "start_time": format_time(start),
            "end_time": format_time(end)
        })
        state = prev_state
        loc = prev_loc
    
    # Reverse to chronological order
    itinerary.reverse()
    
    # Output as JSON
    result = {"itinerary": itinerary}
    print(json.dumps(result))

if __name__ == "__main__":
    main()