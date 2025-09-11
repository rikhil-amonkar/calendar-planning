import json

def main():
    # Define the travel times dictionary
    travel_times = {
        'Chinatown': {
            'Embarcadero': 5,
            'Pacific Heights': 10,
            'Russian Hill': 7,
            'Haight-Ashbury': 19,
            'Golden Gate Park': 23,
            'Fisherman\'s Wharf': 8,
            'Sunset District': 29,
            'The Castro': 22
        },
        'Embarcadero': {
            'Chinatown': 7,
            'Pacific Heights': 11,
            'Russian Hill': 8,
            'Haight-Ashbury': 21,
            'Golden Gate Park': 25,
            'Fisherman\'s Wharf': 6,
            'Sunset District': 30,
            'The Castro': 25
        },
        'Pacific Heights': {
            'Chinatown': 11,
            'Embarcadero': 10,
            'Russian Hill': 7,
            'Haight-Ashbury': 11,
            'Golden Gate Park': 15,
            'Fisherman\'s Wharf': 13,
            'Sunset District': 21,
            'The Castro': 16
        },
        'Russian Hill': {
            'Chinatown': 9,
            'Embarcadero': 8,
            'Pacific Heights': 7,
            'Haight-Ashbury': 17,
            'Golden Gate Park': 21,
            'Fisherman\'s Wharf': 7,
            'Sunset District': 23,
            'The Castro': 21
        },
        'Haight-Ashbury': {
            'Chinatown': 19,
            'Embarcadero': 20,
            'Pacific Heights': 12,
            'Russian Hill': 17,
            'Golden Gate Park': 7,
            'Fisherman\'s Wharf': 23,
            'Sunset District': 15,
            'The Castro': 6
        },
        'Golden Gate Park': {
            'Chinatown': 23,
            'Embarcadero': 25,
            'Pacific Heights': 16,
            'Russian Hill': 19,
            'Haight-Ashbury': 7,
            'Fisherman\'s Wharf': 24,
            'Sunset District': 10,
            'The Castro': 13
        },
        'Fisherman\'s Wharf': {
            'Chinatown': 12,
            'Embarcadero': 8,
            'Pacific Heights': 12,
            'Russian Hill': 7,
            'Haight-Ashbury': 22,
            'Golden Gate Park': 25,
            'Sunset District': 27,
            'The Castro': 27
        },
        'Sunset District': {
            'Chinatown': 30,
            'Embarcadero': 30,
            'Pacific Heights': 21,
            'Russian Hill': 24,
            'Haight-Ashbury': 15,
            'Golden Gate Park': 11,
            'Fisherman\'s Wharf': 29,
            'The Castro': 17
        },
        'The Castro': {
            'Chinatown': 22,
            'Embarcadero': 22,
            'Pacific Heights': 16,
            'Russian Hill': 18,
            'Haight-Ashbury': 6,
            'Golden Gate Park': 11,
            'Fisherman\'s Wharf': 24,
            'Sunset District': 17
        }
    }
    
    # Define the list of friends with their constraints
    friends = [
        # (name, location, start_available (min from 9:00), end_available, min_duration)
        ('Richard', 'Embarcadero', 15*60+15, 18*60+45, 90),
        ('Mark', 'Pacific Heights', 15*60, 17*60, 45),
        ('Matthew', 'Russian Hill', 17*60+30, 21*60, 90),
        ('Rebecca', 'Haight-Ashbury', 14*60+45, 18*60, 60),
        ('Melissa', 'Golden Gate Park', 13*60+45, 17*60+30, 90),
        ('Margaret', 'Fisherman\'s Wharf', 14*60+45, 20*60+15, 15),
        ('Emily', 'Sunset District', 15*60+45, 17*60, 45),
        ('George', 'The Castro', 14*60, 16*60+15, 75)
    ]
    
    # Map location names to indices
    locations = [
        'Chinatown',
        'Embarcadero',
        'Pacific Heights',
        'Russian Hill',
        'Haight-Ashbury',
        'Golden Gate Park',
        'Fisherman\'s Wharf',
        'Sunset District',
        'The Castro'
    ]
    location_index = {loc: idx for idx, loc in enumerate(locations)}
    
    n = len(friends)  # number of friends
    num_states = 1 << n
    num_locations = len(locations)
    
    # Initialize DP table and parent table
    dp = [[float('inf')] * num_locations for _ in range(num_states)]
    parent = [[None] * num_locations for _ in range(num_states)]  # (prev_mask, prev_loc, friend_index)
    
    # Start at Chinatown (index0) at time 0
    dp[0][0] = 0
    
    # Dynamic programming
    for mask in range(num_states):
        for loc_idx in range(num_locations):
            if dp[mask][loc_idx] == float('inf'):
                continue
            current_time = dp[mask][loc_idx]
            current_loc = locations[loc_idx]
            for friend_idx in range(n):
                if mask & (1 << friend_idx):
                    continue
                friend = friends[friend_idx]
                friend_loc = friend[1]
                friend_loc_idx = location_index[friend_loc]
                S = friend[2]
                E = friend[3]
                D = friend[4]
                tt = travel_times[current_loc][friend_loc]
                arrival = current_time + tt
                start_time = max(arrival, S)
                if start_time + D <= E:
                    new_mask = mask | (1 << friend_idx)
                    new_time = start_time + D
                    if new_time < dp[new_mask][friend_loc_idx]:
                        dp[new_mask][friend_loc_idx] = new_time
                        parent[new_mask][friend_loc_idx] = (mask, loc_idx, friend_idx)
    
    # Find the state with the most meetings
    best_mask = 0
    best_count = 0
    for mask in range(num_states):
        count = bin(mask).count('1')
        if count > best_count:
            for loc_idx in range(num_locations):
                if dp[mask][loc_idx] < float('inf'):
                    best_mask = mask
                    best_count = count
                    break
    
    # Reconstruct the schedule
    itinerary = []
    current_mask = best_mask
    # Find the ending location for best_mask
    current_loc_idx = None
    for loc_idx in range(num_locations):
        if dp[best_mask][loc_idx] < float('inf'):
            current_loc_idx = loc_idx
            break
    if current_loc_idx is None:
        # No meetings found
        print(json.dumps({"itinerary": []}))
        return
        
    # Backtrack to get the meetings in reverse order
    meetings = []
    while current_mask != 0:
        prev_mask, prev_loc_idx, friend_idx = parent[current_mask][current_loc_idx]
        friend = friends[friend_idx]
        end_time = dp[current_mask][current_loc_idx]
        start_time = end_time - friend[4]
        meetings.append((friend[0], friend[1], start_time, end_time))
        current_mask = prev_mask
        current_loc_idx = prev_loc_idx
    meetings.reverse()
    
    # Convert minutes to time strings
    def format_time(minutes):
        total_minutes = minutes
        hours = 9 + total_minutes // 60
        mins = total_minutes % 60
        return f"{hours}:{mins:02d}"
    
    # Build itinerary JSON
    itinerary_json = []
    for meeting in meetings:
        name, loc, start, end = meeting
        itinerary_json.append({
            "action": "meet",
            "location": loc,
            "person": name,
            "start_time": format_time(start),
            "end_time": format_time(end)
        })
    
    print(json.dumps({"itinerary": itinerary_json}))

if __name__ == '__main__':
    main()