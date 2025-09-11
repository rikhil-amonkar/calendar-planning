def main():
    # Convert all times to minutes since midnight for easier calculation
    def time_to_minutes(time_str):
        hours, minutes = map(int, time_str.split(':'))
        return hours * 60 + minutes

    def minutes_to_time(minutes):
        hours = minutes // 60
        mins = minutes % 60
        return f"{hours}:{mins:02d}"

    # Input parameters
    travel_time = 23  # minutes from Golden Gate Park to Chinatown
    start_location = "Golden Gate Park"
    start_time = time_to_minutes("9:00")
    david_location = "Chinatown"
    david_start = time_to_minutes("16:00")
    david_end = time_to_minutes("21:45")
    min_meeting_duration = 105

    # Calculate latest possible meeting start time
    latest_meeting_start = david_end - min_meeting_duration
    
    # Calculate departure time from Golden Gate Park
    departure_time = latest_meeting_start - travel_time
    
    # Ensure we don't try to meet before David arrives
    if departure_time < start_time:
        departure_time = start_time
        arrival_time = departure_time + travel_time
        meeting_start = max(arrival_time, david_start)
        meeting_end = meeting_start + min_meeting_duration
        if meeting_end > david_end:
            meeting_end = david_end
            meeting_start = meeting_end - min_meeting_duration
    else:
        meeting_start = latest_meeting_start
        meeting_end = meeting_start + min_meeting_duration

    # Create itinerary
    itinerary = []
    if meeting_start >= david_start and meeting_end <= david_end:
        itinerary.append({
            "action": "meet",
            "location": david_location,
            "person": "David",
            "start_time": minutes_to_time(meeting_start),
            "end_time": minutes_to_time(meeting_end)
        })

    # Output as JSON
    import json
    print(json.dumps({"itinerary": itinerary}, indent=2))

if __name__ == "__main__":
    main()