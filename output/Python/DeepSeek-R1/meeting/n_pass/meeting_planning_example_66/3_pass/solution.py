import json

def time_to_minutes(time_str):
    parts = time_str.split(':')
    hours = int(parts[0])
    minutes = int(parts[1]) if len(parts) > 1 else 0
    return hours * 60 + minutes

def minutes_to_time(total_minutes):
    hours = total_minutes // 60
    minutes = total_minutes % 60
    return f"{hours}:{minutes:02d}"

def main():
    # Input parameters
    start_time_str = "9:00"
    start_location = "Nob Hill"
    robert_available_start_str = "11:15"
    robert_available_end_str = "17:45"  # 5:45 PM in 24-hour
    min_meeting_duration = 120  # minutes
    travel_time_to_presidio = 17  # minutes

    # Convert times to minutes since midnight
    start_minutes = time_to_minutes(start_time_str)
    robert_start_minutes = time_to_minutes(robert_available_start_str)
    robert_end_minutes = time_to_minutes(robert_available_end_str)

    # Calculate when to leave Nob Hill to arrive at Presidio by 11:15
    travel_start_minutes = robert_start_minutes - travel_time_to_presidio
    travel_start_time = minutes_to_time(travel_start_minutes)
    travel_end_time = robert_available_start_str  # 11:15

    # Build itinerary
    itinerary = [
        {
            "action": "meet",
            "location": start_location,
            "person": "Self",
            "start_time": start_time_str,
            "end_time": travel_start_time
        },
        {
            "action": "travel",
            "from": start_location,
            "to": "Presidio",
            "start_time": travel_start_time,
            "end_time": travel_end_time
        },
        {
            "action": "meet",
            "location": "Presidio",
            "person": "Robert",
            "start_time": robert_available_start_str,
            "end_time": robert_available_end_str
        }
    ]

    # Output as JSON
    result = {"itinerary": itinerary}
    print(json.dumps(result))

if __name__ == "__main__":
    main()