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
    mi = m % 60
    return f"{h}:{mi:02d}"

def main():
    # Given data
    travel_to_richmond = 12  # Alamo Square -> Richmond District
    travel_to_alamo = 13     # Richmond District -> Alamo Square
    
    start_location = "Alamo Square"
    start_time_str = "9:00"
    
    timothy_location = "Richmond District"
    timothy_start_str = "20:45"
    timothy_end_str = "21:30"
    timothy_min_duration = 45
    
    # Convert to minutes
    start_time = time_to_minutes(start_time_str)
    timothy_start = time_to_minutes(timothy_start_str)
    timothy_end = time_to_minutes(timothy_end_str)
    
    # Check if Timothy's window is long enough
    available_duration = timothy_end - timothy_start
    if available_duration < timothy_min_duration:
        print("Timothy's availability is too short for the required meeting.")
        return
    
    # We'll meet Timothy for exactly 45 minutes starting at 20:45
    meet_start = timothy_start
    meet_end = meet_start + timothy_min_duration
    
    if meet_end > timothy_end:
        meet_end = timothy_end
    
    # We must leave Alamo Square early enough to arrive by meet_start
    depart_alamo = meet_start - travel_to_richmond
    
    # Build itinerary
    itinerary = []
    
    # If there's time between start and departure, we could note free time,
    # but the spec only wants "meet" actions in itinerary.
    # So we just add the Timothy meeting.
    
    itinerary.append({
        "action": "meet",
        "location": timothy_location,
        "person": "Timothy",
        "start_time": minutes_to_time(meet_start),
        "end_time": minutes_to_time(meet_end)
    })
    
    # Output as JSON
    result = {
        "itinerary": itinerary
    }
    
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()