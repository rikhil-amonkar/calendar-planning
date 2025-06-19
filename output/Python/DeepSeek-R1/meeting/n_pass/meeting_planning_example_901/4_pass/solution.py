import json

def minutes_to_time_str(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

def main():
    # Comprehensive travel times between all location pairs (directed graph)
    travel_times = {
        # From Russian Hill
        ("Russian Hill", "Pacific Heights"): 7,
        ("Russian Hill", "North Beach"): 5,
        ("Russian Hill", "Golden Gate Park"): 21,
        ("Russian Hill", "Embarcadero"): 8,
        ("Russian Hill", "Haight-Ashbury"): 17,
        ("Russian Hill", "Fisherman's Wharf"): 7,
        ("Russian Hill", "Mission District"): 16,
        ("Russian Hill", "Alamo Square"): 15,
        ("Russian Hill", "Bayview"): 23,
        ("Russian Hill", "Richmond District"): 14,
        
        # From Pacific Heights
        ("Pacific Heights", "Russian Hill"): 7,
        ("Pacific Heights", "North Beach"): 9,
        ("Pacific Heights", "Golden Gate Park"): 15,
        ("Pacific Heights", "Embarcadero"): 10,
        ("Pacific Heights", "Haight-Ashbury"): 11,
        ("Pacific Heights", "Fisherman's Wharf"): 13,
        ("Pacific Heights", "Mission District"): 15,
        ("Pacific Heights", "Alamo Square"): 10,
        ("Pacific Heights", "Bayview"): 22,
        ("Pacific Heights", "Richmond District"): 12,
        
        # From North Beach
        ("North Beach", "Russian Hill"): 4,
        ("North Beach", "Pacific Heights"): 8,
        ("North Beach", "Golden Gate Park"): 22,
        ("North Beach", "Embarcadero"): 6,
        ("North Beach", "Haight-Ashbury"): 18,
        ("North Beach", "Fisherman's Wharf"): 5,
        ("North Beach", "Mission District"): 18,
        ("North Beach", "Alamo Square"): 16,
        ("North Beach", "Bayview"): 25,
        ("North Beach", "Richmond District"): 18,
        
        # From Golden Gate Park
        ("Golden Gate Park", "Russian Hill"): 19,
        ("Golden Gate Park", "Pacific Heights"): 16,
        ("Golden Gate Park", "North Beach"): 23,
        ("Golden Gate Park", "Embarcadero"): 25,
        ("Golden Gate Park", "Haight-Ashbury"): 7,
        ("Golden Gate Park", "Fisherman's Wharf"): 24,
        ("Golden Gate Park", "Mission District"): 17,
        ("Golden Gate Park", "Alamo Square"): 9,
        ("Golden Gate Park", "Bayview"): 23,
        ("Golden Gate Park", "Richmond District"): 7,
        
        # From Embarcadero
        ("Embarcadero", "Russian Hill"): 8,
        ("Embarcadero", "Pacific Heights"): 10,
        ("Embarcadero", "North Beach"): 5,
        ("Embarcadero", "Golden Gate Park"): 25,
        ("Embarcadero", "Haight-Ashbury"): 21,
        ("Embarcadero", "Fisherman's Wharf"): 6,
        ("Embarcadero", "Mission District"): 20,
        ("Embarcadero", "Alamo Square"): 19,
        ("Embarcadero", "Bayview"): 21,
        ("Embarcadero", "Richmond District"): 21,
        
        # From Haight-Ashbury
        ("Haight-Ashbury", "Russian Hill"): 17,
        ("Haight-Ashbury", "Pacific Heights"): 12,
        ("Haight-Ashbury", "North Beach"): 19,
        ("Haight-Ashbury", "Golden Gate Park"): 7,
        ("Haight-Ashbury", "Embarcadero"): 20,
        ("Haight-Ashbury", "Fisherman's Wharf"): 23,
        ("Haight-Ashbury", "Mission District"): 11,
        ("Haight-Ashbury", "Alamo Square"): 5,
        ("Haight-Ashbury", "Bayview"): 18,
        ("Haight-Ashbury", "Richmond District"): 10,
        
        # From Fisherman's Wharf
        ("Fisherman's Wharf", "Russian Hill"): 7,
        ("Fisherman's Wharf", "Pacific Heights"): 12,
        ("Fisherman's Wharf", "North Beach"): 6,
        ("Fisherman's Wharf", "Golden Gate Park"): 25,
        ("Fisherman's Wharf", "Embarcadero"): 8,
        ("Fisherman's Wharf", "Haight-Ashbury"): 22,
        ("Fisherman's Wharf", "Mission District"): 22,
        ("Fisherman's Wharf", "Alamo Square"): 21,
        ("Fisherman's Wharf", "Bayview"): 26,
        ("Fisherman's Wharf", "Richmond District"): 18,
        
        # From Mission District
        ("Mission District", "Russian Hill"): 15,
        ("Mission District", "Pacific Heights"): 16,
        ("Mission District", "North Beach"): 17,
        ("Mission District", "Golden Gate Park"): 17,
        ("Mission District", "Embarcadero"): 19,
        ("Mission District", "Haight-Ashbury"): 12,
        ("Mission District", "Fisherman's Wharf"): 22,
        ("Mission District", "Alamo Square"): 11,
        ("Mission District", "Bayview"): 14,
        ("Mission District", "Richmond District"): 20,
        
        # From Alamo Square
        ("Alamo Square", "Russian Hill"): 13,
        ("Alamo Square", "Pacific Heights"): 10,
        ("Alamo Square", "North Beach"): 15,
        ("Alamo Square", "Golden Gate Park"): 9,
        ("Alamo Square", "Embarcadero"): 16,
        ("Alamo Square", "Haight-Ashbury"): 5,
        ("Alamo Square", "Fisherman's Wharf"): 19,
        ("Alamo Square", "Mission District"): 10,
        ("Alamo Square", "Bayview"): 16,
        ("Alamo Square", "Richmond District"): 11,
        
        # From Bayview
        ("Bayview", "Russian Hill"): 23,
        ("Bayview", "Pacific Heights"): 23,
        ("Bayview", "North Beach"): 22,
        ("Bayview", "Golden Gate Park"): 22,
        ("Bayview", "Embarcadero"): 19,
        ("Bayview", "Haight-Ashbury"): 19,
        ("Bayview", "Fisherman's Wharf"): 25,
        ("Bayview", "Mission District"): 13,
        ("Bayview", "Alamo Square"): 16,
        ("Bayview", "Richmond District"): 25,
        
        # From Richmond District
        ("Richmond District", "Russian Hill"): 13,
        ("Richmond District", "Pacific Heights"): 10,
        ("Richmond District", "North Beach"): 17,
        ("Richmond District", "Golden Gate Park"): 9,
        ("Richmond District", "Embarcadero"): 19,
        ("Richmond District", "Haight-Ashbury"): 10,
        ("Richmond District", "Fisherman's Wharf"): 18,
        ("Richmond District", "Mission District"): 20,
        ("Richmond District", "Alamo Square"): 13,
        ("Richmond District", "Bayview"): 27
    }
    
    # Add self-loop travel times (0 minutes)
    locations = [
        "Russian Hill", "Pacific Heights", "North Beach", "Golden Gate Park", "Embarcadero",
        "Haight-Ashbury", "Fisherman's Wharf", "Mission District", "Alamo Square", "Bayview", "Richmond District"
    ]
    for loc in locations:
        travel_times[(loc, loc)] = 0

    # Define friends with their constraints (times in minutes from midnight)
    friends = [
        {"name": "Emily", "location": "Pacific Heights", "start": 9*60+15, "end": 13*60+45, "min_duration": 120},
        {"name": "Helen", "location": "North Beach", "start": 13*60+45, "end": 18*60+45, "min_duration": 30},
        {"name": "Kimberly", "location": "Golden Gate Park", "start": 18*60+45, "end": 21*60+15, "min_duration": 75},
        {"name": "James", "location": "Embarcadero", "start": 10*60+30, "end": 11*60+30, "min_duration": 30},
        {"name": "Linda", "location": "Haight-Ashbury", "start": 7*60+30, "end": 19*60+15, "min_duration": 15},
        {"name": "Paul", "location": "Fisherman's Wharf", "start": 14*60+45, "end": 18*60+45, "min_duration": 90},
        {"name": "Anthony", "location": "Mission District", "start": 8*60+0, "end": 14*60+45, "min_duration": 105},
        {"name": "Nancy", "location": "Alamo Square", "start": 8*60+30, "end": 13*60+45, "min_duration": 120},
        {"name": "William", "location": "Bayview", "start": 17*60+30, "end": 20*60+30, "min_duration": 120},
        {"name": "Margaret", "location": "Richmond District", "start": 15*60+15, "end": 18*60+15, "min_duration": 45}
    ]
    
    n = len(friends)
    start_loc = "Russian Hill"
    start_time = 9 * 60  # 9:00 AM in minutes
    end_of_day = 21 * 60  # 21:00 (9:00 PM)

    # Initialize DP dictionary
    dp = {}
    initial_state = (0, start_loc)  # mask=0, current_location=start_loc
    dp[initial_state] = {
        'time': start_time,
        'prev': None,
        'last_friend': None,
        'start_time': None,
        'end_time': None
    }
    
    best_state = initial_state
    max_count = 0
    
    # Iterate over all masks
    for mask in range(1 << n):
        for loc in locations:
            state = (mask, loc)
            if state not in dp:
                continue
            current_time = dp[state]['time']
            # Try to extend to each unvisited friend
            for j in range(n):
                if mask & (1 << j):
                    continue
                friend = friends[j]
                to_loc = friend['location']
                travel_key = (loc, to_loc)
                if travel_key not in travel_times:
                    continue
                travel_time = travel_times[travel_key]
                arrival_time = current_time + travel_time
                meeting_start = max(arrival_time, friend['start'])
                meeting_end = meeting_start + friend['min_duration']
                
                # Check if meeting can be scheduled within friend's window and before end_of_day
                if meeting_end > friend['end'] or meeting_end > end_of_day:
                    continue
                
                new_mask = mask | (1 << j)
                new_state = (new_mask, to_loc)
                new_time = meeting_end
                
                # Update DP state if new_state not seen or found earlier finish time
                if new_state not in dp or new_time < dp[new_state]['time']:
                    dp[new_state] = {
                        'time': new_time,
                        'prev': state,
                        'last_friend': j,
                        'start_time': meeting_start,
                        'end_time': meeting_end
                    }
                    # Update best_state if more meetings or same meetings with earlier finish
                    current_count = bin(new_mask).count("1")
                    if current_count > max_count or (current_count == max_count and new_time < dp[best_state]['time']):
                        max_count = current_count
                        best_state = new_state
    
    # Backtrack to build itinerary
    itinerary_entries = []
    current_state = best_state
    while current_state != initial_state:
        state_info = dp[current_state]
        j = state_info['last_friend']
        friend = friends[j]
        itinerary_entries.append({
            'action': 'meet',
            'location': friend['location'],
            'person': friend['name'],
            'start_time': state_info['start_time'],
            'end_time': state_info['end_time']
        })
        current_state = state_info['prev']
    
    # Reverse to get chronological order
    itinerary_entries.reverse()
    
    # Convert times to string format
    for entry in itinerary_entries:
        entry['start_time'] = minutes_to_time_str(entry['start_time'])
        entry['end_time'] = minutes_to_time_str(entry['end_time'])
    
    # Output as JSON
    result = {"itinerary": itinerary_entries}
    print(json.dumps(result))

if __name__ == '__main__':
    main()