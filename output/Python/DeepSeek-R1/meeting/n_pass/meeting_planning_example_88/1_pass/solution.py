import json

def time_to_minutes(time_str):
    parts = time_str.split(':')
    hour = int(parts[0])
    minutes = int(parts[1]) if len(parts) > 1 else 0
    return hour * 60 + minutes

def minutes_to_time(mins):
    hour = mins // 60
    minutes = mins % 60
    return f"{hour}:{minutes:02d}"

def main():
    # Input parameters
    start_location = "Sunset District"
    start_time_str = "9:00"
    joshua_location = "Golden Gate Park"
    joshua_person = "Joshua"
    joshua_available_start_str = "20:45"
    joshua_available_end_str = "21:45"
    min_meeting_duration = 15
    travel_time_to_ggp = 11  # Sunset District to Golden Gate Park

    # Convert times to minutes
    start_minutes = time_to_minutes(start_time_str)
    joshua_start_minutes = time_to_minutes(joshua_available_start_str)
    joshua_end_minutes = time_to_minutes(joshua_available_end_str)
    
    # Calculate latest departure time from Sunset District
    latest_departure = joshua_start_minutes - travel_time_to_ggp
    
    # Ensure we can meet for at least min_meeting_duration
    meeting_duration = joshua_end_minutes - joshua_start_minutes
    if latest_departure < start_minutes:
        # Not feasible to meet Joshua due to travel constraints
        itinerary = []
    elif meeting_duration < min_meeting_duration:
        # Not enough time to meet minimum duration
        itinerary = []
    else:
        # Schedule the meeting for Joshua's entire available window
        itinerary = [
            {
                "action": "meet",
                "location": joshua_location,
                "person": joshua_person,
                "start_time": minutes_to_time(joshua_start_minutes),
                "end_time": minutes_to_time(joshua_end_minutes)
            }
        ]
    
    # Output as JSON
    result = {"itinerary": itinerary}
    print(json.dumps(result))

if __name__ == "__main__":
    main()