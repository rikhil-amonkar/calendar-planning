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
    # Travel times in minutes: from -> to -> time
    travel_times = {
        ("North Beach", "Union Square"): 7,
        ("North Beach", "Russian Hill"): 4,
        ("Union Square", "North Beach"): 10,
        ("Union Square", "Russian Hill"): 13,
        ("Russian Hill", "North Beach"): 5,
        ("Russian Hill", "Union Square"): 11,
    }
    
    # Initial conditions
    current_location = "North Beach"
    current_time = time_to_minutes("9:00")
    
    # Friend constraints
    emily_location = "Union Square"
    emily_start = time_to_minutes("16:00")
    emily_end = time_to_minutes("17:15")
    emily_min_duration = 45
    
    margaret_location = "Russian Hill"
    margaret_start = time_to_minutes("19:00")
    margaret_end = time_to_minutes("21:00")
    margaret_min_duration = 120
    
    itinerary = []
    
    # Step 1: Go to Emily by her start time
    travel_to_emily = travel_times[(current_location, emily_location)]
    # We want to arrive exactly at emily_start
    depart_time = emily_start - travel_to_emily
    if depart_time < current_time:
        # If we need to leave earlier than now, we must wait at current location until depart_time
        # But here, we have plenty of time, so we can leave now and wait there.
        # Let's leave now and arrive early, then wait at Union Square.
        arrival_at_emily = current_time + travel_to_emily
        if arrival_at_emily < emily_start:
            # Wait at Union Square
            pass
        # Update current time to arrival time
        current_time = arrival_at_emily
        current_location = emily_location
    else:
        # Wait at current location until depart_time, then travel
        # For simplicity, assume we leave now and arrive early
        arrival_at_emily = current_time + travel_to_emily
        current_time = arrival_at_emily
        current_location = emily_location
    
    # Wait until Emily's start time if we arrived early
    if current_time < emily_start:
        current_time = emily_start
    
    # Meet Emily for 45 minutes
    emily_meeting_end = current_time + emily_min_duration
    itinerary.append({
        "action": "meet",
        "location": emily_location,
        "person": "Emily",
        "start_time": minutes_to_time(current_time),
        "end_time": minutes_to_time(emily_meeting_end)
    })
    
    # Step 2: Travel to Margaret
    current_location = emily_location
    current_time = emily_meeting_end
    travel_to_margaret = travel_times[(current_location, margaret_location)]
    arrival_at_margaret = current_time + travel_to_margaret
    current_location = margaret_location
    current_time = arrival_at_margaret
    
    # Wait until Margaret's start time if early
    if current_time < margaret_start:
        current_time = margaret_start
    
    # Meet Margaret for 120 minutes
    margaret_meeting_end = current_time + margaret_min_duration
    if margaret_meeting_end > margaret_end:
        margaret_meeting_end = margaret_end  # cap at her availability
    
    itinerary.append({
        "action": "meet",
        "location": margaret_location,
        "person": "Margaret",
        "start_time": minutes_to_time(current_time),
        "end_time": minutes_to_time(margaret_meeting_end)
    })
    
    # Output as JSON
    result = {"itinerary": itinerary}
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()