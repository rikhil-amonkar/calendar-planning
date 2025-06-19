import json
from itertools import combinations, permutations, chain

def main():
    # Travel times dictionary (directed graph)
    travel_times = {
        "Union Square": {"Nob Hill": 9, "Haight-Ashbury": 18, "Chinatown": 7, "Marina District": 18},
        "Nob Hill": {"Union Square": 7, "Haight-Ashbury": 13, "Chinatown": 6, "Marina District": 11},
        "Haight-Ashbury": {"Union Square": 17, "Nob Hill": 15, "Chinatown": 19, "Marina District": 17},
        "Chinatown": {"Union Square": 7, "Nob Hill": 8, "Haight-Ashbury": 19, "Marina District": 12},
        "Marina District": {"Union Square": 16, "Nob Hill": 12, "Haight-Ashbury": 16, "Chinatown": 16}
    }
    
    # Friends data: convert availability times to minutes since midnight
    friends = [
        {"name": "Karen", "location": "Nob Hill", "start_avail": 21*60+15, "end_avail": 21*60+45, "min_duration": 30},
        {"name": "Joseph", "location": "Haight-Ashbury", "start_avail": 12*60+30, "end_avail": 19*60+45, "min_duration": 90},
        {"name": "Sandra", "location": "Chinatown", "start_avail": 7*60+15, "end_avail": 19*60+15, "min_duration": 75},
        {"name": "Nancy", "location": "Marina District", "start_avail": 11*60, "end_avail": 20*60+15, "min_duration": 105}
    ]
    
    start_time_minutes = 9 * 60  # 9:00 AM
    start_location = "Union Square"
    
    best_count = 0
    best_schedule = None
    
    # Generate all non-empty subsets of friends
    all_subsets = chain.from_iterable(combinations(friends, r) for r in range(1, len(friends)+1))
    
    for subset in all_subsets:
        for order in permutations(subset):
            current_time = start_time_minutes
            current_loc = start_location
            schedule = []
            valid = True
            
            for friend in order:
                # Get travel time from current_loc to friend's location
                try:
                    travel_time = travel_times[current_loc][friend["location"]]
                except KeyError:
                    valid = False
                    break
                
                # Calculate arrival time at friend's location
                arrival = current_time + travel_time
                # Meeting can start at the later of arrival or friend's available start time
                meeting_start = max(arrival, friend["start_avail"])
                meeting_end = meeting_start + friend["min_duration"]
                
                # Check if meeting fits within friend's availability
                if meeting_end > friend["end_avail"]:
                    valid = False
                    break
                
                # Record meeting details
                schedule.append({
                    "friend": friend,
                    "start": meeting_start,
                    "end": meeting_end
                })
                
                # Update current time and location after meeting
                current_time = meeting_end
                current_loc = friend["location"]
            
            if valid:
                if len(subset) > best_count:
                    best_count = len(subset)
                    best_schedule = schedule
                # If we've scheduled all friends, we can break early (since we want max count)
                if best_count == len(friends):
                    break
        if best_count == len(friends):
            break
    
    # If no valid schedule found (shouldn't happen for this problem), use empty itinerary
    if best_schedule is None:
        itinerary = []
    else:
        itinerary = []
        for event in best_schedule:
            friend = event["friend"]
            start_min = event["start"]
            end_min = event["end"]
            
            # Convert minutes to time string (H:MM format)
            start_hour = start_min // 60
            start_minute = start_min % 60
            start_str = f"{start_hour}:{start_minute:02d}"
            
            end_hour = end_min // 60
            end_minute = end_min % 60
            end_str = f"{end_hour}:{end_minute:02d}"
            
            itinerary.append({
                "action": "meet",
                "location": friend["location"],
                "person": friend["name"],
                "start_time": start_str,
                "end_time": end_str
            })
    
    # Output as JSON
    result = {"itinerary": itinerary}
    print(json.dumps(result))

if __name__ == "__main__":
    main()