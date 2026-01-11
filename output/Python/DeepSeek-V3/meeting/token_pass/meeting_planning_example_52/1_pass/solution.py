import json

def minutes_to_str(minutes):
    """Convert minutes since midnight to 'H:MM' format."""
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

def str_to_minutes(time_str):
    """Convert 'H:MM' to minutes since midnight."""
    h, m = map(int, time_str.split(':'))
    return h * 60 + m

def main():
    # Input parameters
    start_location = "Russian Hill"
    start_time_str = "9:00"
    barbara_location = "Richmond District"
    barbara_start_str = "13:15"
    barbara_end_str = "18:15"
    min_meeting_duration = 45  # minutes
    
    travel_to_richmond = 14  # minutes
    travel_to_russian = 13   # minutes
    
    # Convert times to minutes
    current_time = str_to_minutes(start_time_str)
    barbara_start = str_to_minutes(barbara_start_str)
    barbara_end = str_to_minutes(barbara_end_str)
    
    itinerary = []
    
    # 1. Travel from Russian Hill to Richmond District
    travel_start = current_time
    travel_end = current_time + travel_to_richmond
    itinerary.append({
        "action": "travel",
        "location": "Richmond District",
        "person": None,
        "start_time": minutes_to_str(travel_start),
        "end_time": minutes_to_str(travel_end)
    })
    
    current_time = travel_end  # 9:14
    
    # 2. Wait until Barbara is available
    if current_time < barbara_start:
        itinerary.append({
            "action": "wait",
            "location": "Richmond District",
            "person": None,
            "start_time": minutes_to_str(current_time),
            "end_time": minutes_to_str(barbara_start)
        })
        current_time = barbara_start
    
    # 3. Meet Barbara
    # We can meet for the entire remaining window
    meeting_end = barbara_end
    # Ensure meeting is at least min_meeting_duration
    if meeting_end - current_time < min_meeting_duration:
        meeting_end = current_time + min_meeting_duration
        if meeting_end > barbara_end:
            meeting_end = barbara_end  # but this would fail constraint
    
    itinerary.append({
        "action": "meet",
        "location": barbara_location,
        "person": "Barbara",
        "start_time": minutes_to_str(current_time),
        "end_time": minutes_to_str(meeting_end)
    })
    
    current_time = meeting_end
    
    # 4. Optionally travel back to Russian Hill
    # The problem doesn't require it, but we can add if we want.
    # We'll skip it to stay with Barbara as long as possible.
    
    # Output as JSON
    result = {"itinerary": itinerary}
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()