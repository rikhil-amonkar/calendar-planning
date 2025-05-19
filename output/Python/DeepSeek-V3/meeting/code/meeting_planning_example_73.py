import json

def calculate_optimal_schedule():
    # Input parameters
    arrival_time = "9:00"
    arrival_location = "Russian Hill"
    barbara_available_start = "7:15"
    barbara_available_end = "22:00"
    barbara_location = "Pacific Heights"
    travel_time_to_pacific_heights = 7  # minutes
    meeting_duration = 60  # minutes

    # Convert time strings to minutes since midnight
    def time_to_minutes(time_str):
        hours, minutes = map(int, time_str.split(':'))
        return hours * 60 + minutes

    arrival_min = time_to_minutes(arrival_time)
    barbara_start_min = time_to_minutes(barbara_available_start)
    barbara_end_min = time_to_minutes(barbara_available_end)

    # Calculate earliest possible meeting start time
    earliest_meeting_start = arrival_min + travel_time_to_pacific_heights
    if earliest_meeting_start < barbara_start_min:
        earliest_meeting_start = barbara_start_min

    # Calculate latest possible meeting end time
    latest_meeting_end = barbara_end_min

    # Check if meeting is possible
    if earliest_meeting_start + meeting_duration > latest_meeting_end:
        return {"itinerary": []}

    # Schedule the meeting as early as possible
    meeting_start = earliest_meeting_start
    meeting_end = meeting_start + meeting_duration

    # Convert minutes back to time string
    def minutes_to_time(minutes):
        hours = minutes // 60
        mins = minutes % 60
        return f"{hours}:{mins:02d}"

    itinerary = [
        {
            "action": "meet",
            "location": barbara_location,
            "person": "Barbara",
            "start_time": minutes_to_time(meeting_start),
            "end_time": minutes_to_time(meeting_end)
        }
    ]

    return {"itinerary": itinerary}

result = calculate_optimal_schedule()
print(json.dumps(result, indent=2))