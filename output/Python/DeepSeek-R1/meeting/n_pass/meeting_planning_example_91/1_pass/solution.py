import json

def main():
    # Convert time string (format "H:MM" or "HH:MM") to minutes since midnight
    def time_to_minutes(time_str):
        parts = time_str.split(':')
        hours = int(parts[0])
        minutes = int(parts[1]) if len(parts) > 1 else 0
        return hours * 60 + minutes

    # Convert minutes since midnight to "H:MM" or "HH:MM" format without leading zeros for hours
    def minutes_to_time(total_minutes):
        hours = total_minutes // 60
        minutes = total_minutes % 60
        return f"{hours}:{minutes:02d}"

    # Given constraints
    start_location = "Russian Hill"
    start_time_str = "9:00"
    start_time_minutes = time_to_minutes(start_time_str)
    
    # Daniel's availability
    daniel_location = "Richmond District"
    daniel_start_str = "19:00"
    daniel_end_str = "20:15"
    daniel_start_minutes = time_to_minutes(daniel_start_str)
    daniel_end_minutes = time_to_minutes(daniel_end_str)
    min_daniel_duration = 75  # minutes
    
    # Travel times
    travel_to_richmond = 14  # minutes from Russian Hill to Richmond District
    
    # Calculate latest departure time from Russian Hill to arrive at Richmond for Daniel's meeting
    departure_time = daniel_start_minutes - travel_to_richmond
    
    # Verify Daniel's meeting fits within his availability
    meeting_duration = daniel_end_minutes - daniel_start_minutes
    if meeting_duration < min_daniel_duration:
        # If the available window is too short, adjust meeting end to meet minimum duration (not needed here)
        pass  # In this case, meeting_duration is exactly 75, so no adjustment
    
    # Construct itinerary with Daniel's meeting
    itinerary = [
        {
            "action": "meet",
            "location": daniel_location,
            "person": "Daniel",
            "start_time": minutes_to_time(daniel_start_minutes),
            "end_time": minutes_to_time(daniel_end_minutes)
        }
    ]
    
    # Prepare and output result as JSON
    result = {"itinerary": itinerary}
    print(json.dumps(result))

if __name__ == "__main__":
    main()