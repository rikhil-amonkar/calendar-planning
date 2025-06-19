import json

def time_to_minutes(time_str):
    parts = time_str.split(':')
    return int(parts[0]) * 60 + int(parts[1])

def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}".replace(':0', ':') if mins < 10 else f"{hours}:{mins}"

def main():
    # Input parameters
    start_location = "Fisherman's Wharf"
    start_time_str = "9:00"
    kenneth_location = "Nob Hill"
    kenneth_start_str = "14:15"
    kenneth_end_str = "19:45"
    min_duration = 90
    travel_time = 11  # minutes from Fisherman's Wharf to Nob Hill

    # Convert times to minutes since midnight
    start_minutes = time_to_minutes(start_time_str)
    kenneth_start = time_to_minutes(kenneth_start_str)
    kenneth_end = time_to_minutes(kenneth_end_str)
    
    # Calculate latest possible meeting start time (must end by kenneth_end)
    meeting_end = kenneth_end
    meeting_start = meeting_end - min_duration
    
    # Calculate departure time from start location
    departure_time = meeting_start - travel_time
    
    # Ensure meeting fits in Kenneth's window and we can arrive on time
    if meeting_start < kenneth_start:
        meeting_start = kenneth_start
        meeting_end = meeting_start + min_duration
    
    # Convert times back to string format
    meeting_start_str = minutes_to_time(meeting_start)
    meeting_end_str = minutes_to_time(meeting_end)
    
    # Build itinerary
    itinerary = [
        {
            "action": "meet",
            "location": kenneth_location,
            "person": "Kenneth",
            "start_time": meeting_start_str,
            "end_time": meeting_end_str
        }
    ]
    
    # Output as JSON
    result = {"itinerary": itinerary}
    print(json.dumps(result))

if __name__ == "__main__":
    main()