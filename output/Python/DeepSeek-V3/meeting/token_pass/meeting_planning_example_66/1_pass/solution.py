import json

def time_to_minutes(t):
    """Convert 'H:MM' or 'HH:MM' string to minutes since midnight."""
    hours, minutes = map(int, t.split(':'))
    return hours * 60 + minutes

def minutes_to_time(m):
    """Convert minutes since midnight to 'H:MM' or 'HH:MM' string."""
    hours = m // 60
    minutes = m % 60
    return f"{hours}:{minutes:02d}"

def main():
    # Given data
    travel_nob_to_presidio = 17  # minutes
    travel_presidio_to_nob = 18  # minutes
    
    start_location = "Nob Hill"
    start_time_str = "9:00"
    start_time = time_to_minutes(start_time_str)
    
    robert_location = "Presidio"
    robert_start_str = "11:15"
    robert_end_str = "17:45"
    robert_start = time_to_minutes(robert_start_str)
    robert_end = time_to_minutes(robert_end_str)
    
    min_meeting_duration = 120  # minutes
    
    # We must be at Presidio by robert_start
    # Travel from Nob Hill takes travel_nob_to_presidio minutes
    departure_time = robert_start - travel_nob_to_presidio
    
    # If departure_time is earlier than start_time, we can't leave before we arrive,
    # but here start_time is 9:00, departure_time is 10:58, so it's fine.
    # If departure_time < start_time, we'd have to leave immediately, but that's not the case.
    
    # Meeting duration if we stay until Robert leaves
    meeting_duration = robert_end - robert_start
    
    # Check if meeting duration meets minimum
    if meeting_duration < min_meeting_duration:
        # Not enough time, but here it's plenty
        pass
    
    # Build itinerary
    itinerary = []
    
    # Only add the actual meeting event
    itinerary.append({
        "action": "meet",
        "location": robert_location,
        "person": "Robert",
        "start_time": robert_start_str,
        "end_time": robert_end_str
    })
    
    # Output as JSON
    result = {
        "itinerary": itinerary
    }
    
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()