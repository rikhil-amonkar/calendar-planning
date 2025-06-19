import json

def time_to_minutes(time_str):
    parts = time_str.split(':')
    return int(parts[0]) * 60 + int(parts[1])

def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}" if mins >= 10 else f"{hours}:0{mins}"

def main():
    # Input parameters
    start_location = "Fisherman's Wharf"
    start_time_str = "9:00"
    kenneth_location = "Nob Hill"
    kenneth_start_str = "14:15"
    kenneth_end_str = "19:45"
    min_duration = 90  # minutes
    travel_time = 11   # minutes

    # Convert times to minutes since midnight
    start_minutes = time_to_minutes(start_time_str)  # 9:00 -> 540 minutes
    kenneth_start = time_to_minutes(kenneth_start_str)  # 14:15 -> 855 minutes
    kenneth_end = time_to_minutes(kenneth_end_str)    # 19:45 -> 1185 minutes

    # Calculate earliest possible meeting start time
    earliest_arrival = start_minutes + travel_time  # 9:00 + 11 min = 9:11 (551 minutes)
    meeting_start = max(earliest_arrival, kenneth_start)
    meeting_duration = kenneth_end - meeting_start

    # Check if meeting is possible
    if meeting_duration < min_duration:
        itinerary = []  # impossible to meet for required duration
    else:
        # Calculate travel times
        travel_start = meeting_start - travel_time
        travel_end = meeting_start

        # Create itinerary with travel and meeting events
        itinerary = [
            {
                "action": "travel",
                "from": start_location,
                "to": kenneth_location,
                "start_time": minutes_to_time(travel_start),
                "end_time": minutes_to_time(travel_end)
            },
            {
                "action": "meet",
                "location": kenneth_location,
                "person": "Kenneth",
                "start_time": minutes_to_time(meeting_start),
                "end_time": minutes_to_time(kenneth_end)
            }
        ]
    
    # Output as JSON
    result = {"itinerary": itinerary}
    print(json.dumps(result))

if __name__ == "__main__":
    main()