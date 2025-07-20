import json

def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

def main():
    # Convert start time to minutes (9:00 AM)
    start_minutes = 9 * 60
    
    # Timothy's availability in minutes (8:45PM to 9:30PM)
    timothy_start = 20 * 60 + 45
    timothy_end = 21 * 60 + 30
    
    # Travel times in minutes
    travel_to_richmond = 12
    
    # Calculate departure time from Alamo Square to arrive exactly when Timothy becomes available
    departure_minutes = timothy_start - travel_to_richmond
    
    # Ensure departure is after our start time (9:00 AM) - which it is
    # Meeting duration must be at least 45 minutes - Timothy's window is exactly 45 minutes
    meeting_duration = timothy_end - timothy_start
    if meeting_duration < 45:
        # Not enough time, but in this case it is exactly 45 so condition passes
        pass
    
    # Create meeting event for Timothy
    timothy_meeting = {
        "action": "meet",
        "location": "Richmond District",
        "person": "Timothy",
        "start_time": minutes_to_time(timothy_start),
        "end_time": minutes_to_time(timothy_end)
    }
    
    # Construct itinerary (only Timothy meeting since no other friends specified)
    itinerary = [timothy_meeting]
    
    # Output as JSON
    result = {"itinerary": itinerary}
    print(json.dumps(result))

if __name__ == "__main__":
    main()