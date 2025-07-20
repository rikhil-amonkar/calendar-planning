import json

def main():
    # Convert time string to minutes since midnight
    def time_to_minutes(time_str):
        parts = time_str.split(':')
        hours = int(parts[0])
        minutes = int(parts[1]) if len(parts) > 1 else 0
        return hours * 60 + minutes

    # Convert minutes since midnight to "H:MM" format string
    def minutes_to_time(total_minutes):
        hours = total_minutes // 60
        minutes = total_minutes % 60
        return f"{hours}:{minutes:02d}"

    # Input parameters
    start_time_str = "9:00"
    travel_time_to_chinatown = 23  # minutes
    david_location = "Chinatown"
    david_start_str = "16:00"
    david_end_str = "21:45"
    min_meeting_duration = 105  # minutes

    # Convert times to minutes
    start_minutes = time_to_minutes(start_time_str)
    david_start_minutes = time_to_minutes(david_start_str)
    david_end_minutes = time_to_minutes(david_end_str)

    # Calculate departure time from Golden Gate Park to arrive at Chinatown by 16:00
    departure_minutes = david_start_minutes - travel_time_to_chinatown
    if departure_minutes < start_minutes:
        departure_minutes = start_minutes

    # The meeting starts at 16:00 and ends at 21:45
    meeting_start_minutes = david_start_minutes
    meeting_end_minutes = david_end_minutes

    # Format meeting times
    meeting_start_str = minutes_to_time(meeting_start_minutes)
    meeting_end_str = minutes_to_time(meeting_end_minutes)

    # Create itinerary
    itinerary = [
        {
            "action": "meet",
            "location": david_location,
            "person": "David",
            "start_time": meeting_start_str,
            "end_time": meeting_end_str
        }
    ]

    # Output result as JSON
    result = {"itinerary": itinerary}
    print(json.dumps(result))

if __name__ == "__main__":
    main()