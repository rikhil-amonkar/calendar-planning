import json

def time_to_minutes(t):
    """Convert 'H:MM' string to minutes since midnight."""
    if isinstance(t, str):
        h, m = map(int, t.split(':'))
        return h * 60 + m
    return t

def minutes_to_time(m):
    """Convert minutes since midnight to 'H:MM' string."""
    h = m // 60
    mi = m % 60
    return f"{h}:{mi:02d}"

def main():
    # Travel times in minutes: matrix[from][to]
    locations = ["Bayview", "Embarcadero", "Richmond District", "Fisherman's Wharf"]
    loc_index = {loc: i for i, loc in enumerate(locations)}
    
    travel = [[0, 19, 25, 25],
              [21, 0, 21, 6],
              [26, 19, 0, 18],
              [26, 8, 18, 0]]
    
    # Constraints
    start_loc = "Bayview"
    start_time = "9:00"
    
    friends = [
        {"name": "Jessica", "location": "Embarcadero", "window_start": "16:45", "window_end": "19:00", "min_duration": 30},
        {"name": "Sandra", "location": "Richmond District", "window_start": "18:30", "window_end": "21:45", "min_duration": 120},
        {"name": "Jason", "location": "Fisherman's Wharf", "window_start": "16:00", "window_end": "16:45", "min_duration": 30}
    ]
    
    # We'll try the only feasible order: Jason -> Jessica -> Sandra
    order = ["Jason", "Jessica", "Sandra"]
    # Map name to friend data
    friend_map = {f["name"]: f for f in friends}
    
    itinerary = []
    current_loc = start_loc
    current_time = time_to_minutes(start_time)
    
    # Free time until first meeting
    # We need to be at Jason's location by his window start
    first_friend = friend_map["Jason"]
    travel_time = travel[loc_index[current_loc]][loc_index[first_friend["location"]]]
    arrival_time = current_time + travel_time
    window_start = time_to_minutes(first_friend["window_start"])
    
    if arrival_time > window_start:
        # Can't make it in time
        print("Impossible schedule")
        return
    
    # We can leave early and wait, but let's leave just in time to arrive at window start
    # Actually, to maximize time earlier, we can arrive exactly at window start
    # So leave current location at window_start - travel_time
    # But if that's before current_time, we can leave now (free time before travel).
    # Let's just compute schedule:
    
    # For simplicity, we'll assume we leave to arrive exactly at meeting start time
    # but since we have all free time before, we can arrive earlier and wait.
    # Let's choose to arrive at meeting start time.
    
    for name in order:
        friend = friend_map[name]
        loc = friend["location"]
        window_start_t = time_to_minutes(friend["window_start"])
        window_end_t = time_to_minutes(friend["window_end"])
        min_dur = friend["min_duration"]
        
        # Travel to this friend's location
        travel_time = travel[loc_index[current_loc]][loc_index[loc]]
        arrival_time = current_time + travel_time
        
        # If we arrive before window start, wait
        start_meeting = max(arrival_time, window_start_t)
        end_meeting = start_meeting + min_dur
        
        if end_meeting > window_end_t:
            # Not enough time in window
            print(f"Cannot meet {name} for required duration")
            return
        
        itinerary.append({
            "action": "meet",
            "location": loc,
            "person": name,
            "start_time": minutes_to_time(start_meeting),
            "end_time": minutes_to_time(end_meeting)
        })
        
        current_loc = loc
        current_time = end_meeting
    
    # Output result
    result = {"itinerary": itinerary}
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()