import json

def time_to_minutes(t):
    """Convert 'H:MM' string to minutes since midnight."""
    hours, minutes = map(int, t.split(':'))
    return hours * 60 + minutes

def minutes_to_time(m):
    """Convert minutes since midnight to 'H:MM' string."""
    hours = m // 60
    minutes = m % 60
    return f"{hours}:{minutes:02d}"

def main():
    # Travel times matrix: from_index to to_index
    locations = {"The Castro": 0, "Mission District": 1, "Financial District": 2}
    travel = [
        [0, 7, 20],   # The Castro -> ...
        [7, 0, 17],   # Mission District -> ...
        [23, 17, 0]   # Financial District -> ...
    ]
    
    # Constraints
    start_loc = "The Castro"
    start_time_min = time_to_minutes("9:00")
    
    laura = {
        "location": "Mission District",
        "available_start": time_to_minutes("12:15"),
        "available_end": time_to_minutes("19:45"),
        "min_duration": 75
    }
    
    anthony = {
        "location": "Financial District",
        "available_start": time_to_minutes("12:30"),
        "available_end": time_to_minutes("14:45"),
        "min_duration": 30
    }
    
    friends = [("Laura", laura), ("Anthony", anthony)]
    
    # Try both permutations of meeting order
    best_itinerary = None
    best_end_time = None
    
    from itertools import permutations
    for order in permutations([0, 1]):  # 0=Laura, 1=Anthony
        current_loc = start_loc
        current_time = start_time_min
        itinerary = []
        feasible = True
        
        for idx in order:
            friend_name, friend = friends[idx]
            dest = friend["location"]
            travel_time = travel[locations[current_loc]][locations[dest]]
            arrival = current_time + travel_time
            
            # Wait until friend is available
            start_meeting = max(arrival, friend["available_start"])
            if start_meeting + friend["min_duration"] > friend["available_end"]:
                feasible = False
                break
            
            end_meeting = start_meeting + friend["min_duration"]
            itinerary.append({
                "action": "meet",
                "location": dest,
                "person": friend_name,
                "start_time": minutes_to_time(start_meeting),
                "end_time": minutes_to_time(end_meeting)
            })
            
            current_loc = dest
            current_time = end_meeting
        
        if feasible:
            if best_itinerary is None or current_time < best_end_time:
                best_itinerary = itinerary
                best_end_time = current_time
    
    # Output result
    if best_itinerary is None:
        print("No feasible schedule to meet both friends.")
        return
    
    result = {"itinerary": best_itinerary}
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()