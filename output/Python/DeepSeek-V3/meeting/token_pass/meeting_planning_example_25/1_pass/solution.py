import json

def time_to_minutes(t):
    """Convert 'H:MM' string to minutes since midnight."""
    if isinstance(t, str):
        h, m = map(int, t.split(':'))
        return h * 60 + m
    return t

def minutes_to_time(m):
    """Convert minutes since midnight to 'H:MM' format."""
    h = m // 60
    mm = m % 60
    return f"{h}:{mm:02d}"

def main():
    # Given data
    travel_time = 23  # minutes between locations
    
    start_location = "Golden Gate Park"
    start_time_str = "9:00"
    
    david_location = "Chinatown"
    david_start_str = "16:00"   # 4:00 PM
    david_end_str = "21:45"     # 9:45 PM
    min_meeting_duration = 105  # minutes
    
    # Convert to minutes
    start_time = time_to_minutes(start_time_str)
    david_start = time_to_minutes(david_start_str)
    david_end = time_to_minutes(david_end_str)
    
    # We must travel from Golden Gate Park to Chinatown before meeting David
    # To maximize time with David, we arrive exactly at 4:00 PM
    travel_departure_time = david_start - travel_time
    
    # If travel departure is earlier than start_time, we must wait at start until then
    # But here, start_time is 9:00, travel_departure is 15:37 (3:37 PM), so fine.
    
    # Meeting duration: as long as possible until David leaves
    meeting_duration = david_end - david_start
    
    # Build itinerary
    itinerary = []
    
    # Add initial free time at Golden Gate Park (optional, but shows waiting)
    if travel_departure_time > start_time:
        itinerary.append({
            "action": "free",
            "location": start_location,
            "person": None,
            "start_time": minutes_to_time(start_time),
            "end_time": minutes_to_time(travel_departure_time)
        })
    
    # Travel to Chinatown
    itinerary.append({
        "action": "travel",
        "location": f"{start_location} to {david_location}",
        "person": None,
        "start_time": minutes_to_time(travel_departure_time),
        "end_time": minutes_to_time(david_start)
    })
    
    # Meet David
    itinerary.append({
        "action": "meet",
        "location": david_location,
        "person": "David",
        "start_time": minutes_to_time(david_start),
        "end_time": minutes_to_time(david_end)
    })
    
    # Output as JSON
    result = {
        "itinerary": itinerary
    }
    
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()