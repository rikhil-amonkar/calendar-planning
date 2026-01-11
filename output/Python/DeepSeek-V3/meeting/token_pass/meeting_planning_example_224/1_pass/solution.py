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
    # Travel times in minutes (from -> to)
    travel_times = {
        ("Fisherman's Wharf", "Golden Gate Park"): 25,
        ("Fisherman's Wharf", "Presidio"): 17,
        ("Fisherman's Wharf", "Richmond District"): 18,
        ("Golden Gate Park", "Fisherman's Wharf"): 24,
        ("Golden Gate Park", "Presidio"): 11,
        ("Golden Gate Park", "Richmond District"): 7,
        ("Presidio", "Fisherman's Wharf"): 19,
        ("Presidio", "Golden Gate Park"): 12,
        ("Presidio", "Richmond District"): 7,
        ("Richmond District", "Fisherman's Wharf"): 18,
        ("Richmond District", "Golden Gate Park"): 9,
        ("Richmond District", "Presidio"): 7,
    }

    # Availability and constraints
    # (person, location, available_start, available_end, min_duration_minutes)
    friends = [
        ("Melissa", "Golden Gate Park", "8:30", "20:00", 15),
        ("Nancy", "Presidio", "19:45", "22:00", 105),
        ("Emily", "Richmond District", "16:45", "22:00", 120),
    ]

    # Start at Fisherman's Wharf at 9:00
    current_location = "Fisherman's Wharf"
    current_time = time_to_minutes("9:00")
    
    itinerary = []
    
    # Step 1: Meet Melissa later in the day, just before Emily
    # Leave Fisherman's Wharf at 16:00 to arrive at Golden Gate Park at 16:25
    travel = travel_times[(current_location, "Golden Gate Park")]
    current_time = time_to_minutes("16:00") + travel  # 16:25
    meet_start = current_time
    meet_end = meet_start + friends[0][4]  # 15 min
    itinerary.append({
        "action": "meet",
        "location": friends[0][1],
        "person": friends[0][0],
        "start_time": minutes_to_time(meet_start),
        "end_time": minutes_to_time(meet_end)
    })
    
    # Step 2: Travel to Emily
    current_location = friends[0][1]
    current_time = meet_end
    travel = travel_times[(current_location, friends[2][1])]  # to Richmond District
    current_time += travel  # 16:47
    # Emily available from 16:45, so we can start right away
    meet_start = max(current_time, time_to_minutes(friends[2][2]))
    meet_end = meet_start + friends[2][4]  # 120 min
    itinerary.append({
        "action": "meet",
        "location": friends[2][1],
        "person": friends[2][0],
        "start_time": minutes_to_time(meet_start),
        "end_time": minutes_to_time(meet_end)
    })
    
    # Step 3: Travel to Nancy
    current_location = friends[2][1]
    current_time = meet_end
    travel = travel_times[(current_location, friends[1][1])]  # to Presidio
    current_time += travel  # 18:54
    # Nancy available from 19:45
    meet_start = max(current_time, time_to_minutes(friends[1][2]))
    meet_end = meet_start + friends[1][4]  # 105 min
    itinerary.append({
        "action": "meet",
        "location": friends[1][1],
        "person": friends[1][0],
        "start_time": minutes_to_time(meet_start),
        "end_time": minutes_to_time(meet_end)
    })
    
    # Output as JSON
    result = {"itinerary": itinerary}
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()