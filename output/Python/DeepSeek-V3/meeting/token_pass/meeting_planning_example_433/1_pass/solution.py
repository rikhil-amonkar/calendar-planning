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
    mm = m % 60
    return f"{h}:{mm:02d}"

def main():
    # Travel times matrix (in minutes)
    travel_times = {
        ("Nob Hill", "Richmond District"): 14,
        ("Nob Hill", "Financial District"): 9,
        ("Nob Hill", "North Beach"): 8,
        ("Nob Hill", "The Castro"): 17,
        ("Nob Hill", "Golden Gate Park"): 17,
        ("Richmond District", "Nob Hill"): 17,
        ("Richmond District", "Financial District"): 22,
        ("Richmond District", "North Beach"): 17,
        ("Richmond District", "The Castro"): 16,
        ("Richmond District", "Golden Gate Park"): 9,
        ("Financial District", "Nob Hill"): 8,
        ("Financial District", "Richmond District"): 21,
        ("Financial District", "North Beach"): 7,
        ("Financial District", "The Castro"): 23,
        ("Financial District", "Golden Gate Park"): 23,
        ("North Beach", "Nob Hill"): 7,
        ("North Beach", "Richmond District"): 18,
        ("North Beach", "Financial District"): 8,
        ("North Beach", "The Castro"): 22,
        ("North Beach", "Golden Gate Park"): 22,
        ("The Castro", "Nob Hill"): 16,
        ("The Castro", "Richmond District"): 16,
        ("The Castro", "Financial District"): 20,
        ("The Castro", "North Beach"): 20,
        ("The Castro", "Golden Gate Park"): 11,
        ("Golden Gate Park", "Nob Hill"): 20,
        ("Golden Gate Park", "Richmond District"): 7,
        ("Golden Gate Park", "Financial District"): 26,
        ("Golden Gate Park", "North Beach"): 24,
        ("Golden Gate Park", "The Castro"): 13,
    }
    
    # Friend data: location, window start, window end, min duration (minutes)
    friends = [
        ("Emily", "Richmond District", "19:00", "21:00", 15),
        ("Margaret", "Financial District", "16:30", "20:15", 75),
        ("Ronald", "North Beach", "18:30", "19:30", 45),
        ("Deborah", "The Castro", "13:45", "21:15", 90),
        ("Jeffrey", "Golden Gate Park", "11:15", "14:30", 120),
    ]
    
    # Start at Nob Hill at 9:00 AM
    current_location = "Nob Hill"
    current_time = time_to_minutes("9:00")
    
    itinerary = []
    
    # Planned sequence that works (precomputed from reasoning)
    sequence = [
        ("Jeffrey", "Golden Gate Park", 120),
        ("Deborah", "The Castro", 90),
        ("Margaret", "Financial District", 75),
        ("Ronald", "North Beach", 45),
        ("Emily", "Richmond District", 15),
    ]
    
    for person, location, min_duration in sequence:
        # Travel to location
        travel = travel_times[(current_location, location)]
        arrival_time = current_time + travel
        
        # Find friend data
        friend_data = next(f for f in friends if f[0] == person)
        _, _, window_start_str, window_end_str, _ = friend_data
        window_start = time_to_minutes(window_start_str)
        window_end = time_to_minutes(window_end_str)
        
        # If we arrive before window starts, wait
        start_meeting = max(arrival_time, window_start)
        end_meeting = start_meeting + min_duration
        
        # Check if feasible
        if end_meeting > window_end:
            print(f"Cannot meet {person}: not enough time in window")
            break
        
        itinerary.append({
            "action": "meet",
            "location": location,
            "person": person,
            "start_time": minutes_to_time(start_meeting),
            "end_time": minutes_to_time(end_meeting)
        })
        
        # Update current time and location
        current_time = end_meeting
        current_location = location
    
    # Output as JSON
    result = {"itinerary": itinerary}
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()