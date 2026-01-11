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
    m = m % 60
    return f"{h}:{m:02d}"

def main():
    # Travel times in minutes (from -> to)
    travel = {
        ("Nob Hill", "North Beach"): 8,
        ("Nob Hill", "Fisherman's Wharf"): 11,
        ("Nob Hill", "Bayview"): 19,
        ("North Beach", "Nob Hill"): 7,
        ("North Beach", "Fisherman's Wharf"): 5,
        ("North Beach", "Bayview"): 22,
        ("Fisherman's Wharf", "Nob Hill"): 11,
        ("Fisherman's Wharf", "North Beach"): 6,
        ("Fisherman's Wharf", "Bayview"): 26,
        ("Bayview", "Nob Hill"): 20,
        ("Bayview", "North Beach"): 21,
        ("Bayview", "Fisherman's Wharf"): 25,
    }
    
    # Constraints
    start_location = "Nob Hill"
    start_time = time_to_minutes("9:00")
    
    friends = [
        {
            "name": "Helen",
            "location": "North Beach",
            "available_start": time_to_minutes("7:00"),
            "available_end": time_to_minutes("16:45"),
            "duration": 120,
        },
        {
            "name": "Kimberly",
            "location": "Fisherman's Wharf",
            "available_start": time_to_minutes("16:30"),
            "available_end": time_to_minutes("21:00"),
            "duration": 45,
        },
        {
            "name": "Patricia",
            "location": "Bayview",
            "available_start": time_to_minutes("18:00"),
            "available_end": time_to_minutes("21:15"),
            "duration": 120,
        }
    ]
    
    # We'll brute-force possible start times for Helen and Kimberly within their windows
    # and see if we can fit Patricia.
    best_schedule = []
    max_met = 0
    
    # Try meeting all three in order: Helen -> Kimberly -> Patricia
    helen = friends[0]
    kimberly = friends[1]
    patricia = friends[2]
    
    # Helen's possible start times (every 5 minutes for simplicity)
    for h_start in range(helen["available_start"], helen["available_end"] - helen["duration"] + 1, 5):
        h_end = h_start + helen["duration"]
        # Travel from start_location to Helen's location
        if h_start - travel[(start_location, helen["location"])] < start_time:
            continue  # Can't get there in time from start
        # Travel from Helen to Kimberly
        travel_h_k = travel[(helen["location"], kimberly["location"])]
        k_arrive = h_end + travel_h_k
        if k_arrive > kimberly["available_end"]:
            continue
        # Kimberly's meeting must start at or after her available_start and at or after k_arrive
        k_start = max(kimberly["available_start"], k_arrive)
        if k_start + kimberly["duration"] > kimberly["available_end"]:
            continue
        k_end = k_start + kimberly["duration"]
        # Travel from Kimberly to Patricia
        travel_k_p = travel[(kimberly["location"], patricia["location"])]
        p_arrive = k_end + travel_k_p
        if p_arrive > patricia["available_end"]:
            continue
        p_start = max(patricia["available_start"], p_arrive)
        if p_start + patricia["duration"] > patricia["available_end"]:
            continue
        p_end = p_start + patricia["duration"]
        
        # Valid schedule for all three
        schedule = [
            {"action": "meet", "location": helen["location"], "person": helen["name"],
             "start_time": minutes_to_time(h_start), "end_time": minutes_to_time(h_end)},
            {"action": "meet", "location": kimberly["location"], "person": kimberly["name"],
             "start_time": minutes_to_time(k_start), "end_time": minutes_to_time(k_end)},
            {"action": "meet", "location": patricia["location"], "person": patricia["name"],
             "start_time": minutes_to_time(p_start), "end_time": minutes_to_time(p_end)},
        ]
        best_schedule = schedule
        max_met = 3
        break  # First feasible all-three schedule is optimal (minimizes idle before Helen)
    
    # If can't meet all three, try meeting two (but here we know all three is possible)
    if max_met == 0:
        # Fallback logic: try pairs (not needed here, but kept for completeness)
        pass
    
    # Output
    result = {
        "itinerary": best_schedule
    }
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()