import json

def main():
    # Travel times matrix (in minutes)
    travel_times = {
        ("Golden Gate Park", "Alamo Square"): 10,
        ("Golden Gate Park", "Presidio"): 11,
        ("Golden Gate Park", "Russian Hill"): 19,
        ("Alamo Square", "Golden Gate Park"): 9,
        ("Alamo Square", "Presidio"): 18,
        ("Alamo Square", "Russian Hill"): 13,
        ("Presidio", "Golden Gate Park"): 12,
        ("Presidio", "Alamo Square"): 18,
        ("Presidio", "Russian Hill"): 14,
        ("Russian Hill", "Golden Gate Park"): 21,
        ("Russian Hill", "Alamo Square"): 15,
        ("Russian Hill", "Presidio"): 14,
    }
    
    # Helper: convert H:MM to minutes since midnight
    def to_minutes(t):
        h, m = map(int, t.split(':'))
        return h * 60 + m
    
    # Helper: convert minutes to H:MM
    def to_time_str(m):
        h = m // 60
        mi = m % 60
        return f"{h}:{mi:02d}"
    
    # Constraints
    start_location = "Golden Gate Park"
    start_time_min = to_minutes("9:00")
    
    friends = [
        {
            "name": "Timothy",
            "location": "Alamo Square",
            "window_start": to_minutes("12:00"),
            "window_end": to_minutes("16:15"),
            "min_duration": 105
        },
        {
            "name": "Joseph",
            "location": "Russian Hill",
            "window_start": to_minutes("16:45"),
            "window_end": to_minutes("21:30"),
            "min_duration": 60
        },
        {
            "name": "Mark",
            "location": "Presidio",
            "window_start": to_minutes("18:45"),
            "window_end": to_minutes("21:00"),
            "min_duration": 60
        }
    ]
    
    # Optimal schedule found by reasoning
    # Step 1: Go to Timothy later to reduce idle time
    # Leave start location at 14:20 to arrive at Timothy at 14:30
    current_time = start_time_min
    current_loc = start_location
    
    itinerary = []
    
    # Meeting 1: Timothy
    travel = travel_times[(current_loc, friends[0]["location"])]
    arrival = current_time + travel
    # Start meeting at 14:30 (arrival exactly then)
    meet_start = to_minutes("14:30")
    meet_end = meet_start + friends[0]["min_duration"]
    itinerary.append({
        "action": "meet",
        "location": friends[0]["location"],
        "person": friends[0]["name"],
        "start_time": to_time_str(meet_start),
        "end_time": to_time_str(meet_end)
    })
    
    # Update current time and location after meeting
    current_time = meet_end
    current_loc = friends[0]["location"]
    
    # Meeting 2: Joseph
    travel = travel_times[(current_loc, friends[1]["location"])]
    arrival = current_time + travel
    # Joseph available from 16:45
    meet_start = max(arrival, friends[1]["window_start"])
    meet_end = meet_start + friends[1]["min_duration"]
    itinerary.append({
        "action": "meet",
        "location": friends[1]["location"],
        "person": friends[1]["name"],
        "start_time": to_time_str(meet_start),
        "end_time": to_time_str(meet_end)
    })
    
    current_time = meet_end
    current_loc = friends[1]["location"]
    
    # Meeting 3: Mark
    travel = travel_times[(current_loc, friends[2]["location"])]
    arrival = current_time + travel
    meet_start = max(arrival, friends[2]["window_start"])
    meet_end = meet_start + friends[2]["min_duration"]
    itinerary.append({
        "action": "meet",
        "location": friends[2]["location"],
        "person": friends[2]["name"],
        "start_time": to_time_str(meet_start),
        "end_time": to_time_str(meet_end)
    })
    
    # Output as JSON
    result = {"itinerary": itinerary}
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()