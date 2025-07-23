import json

def calculate_optimal_schedule():
    # Input parameters
    arrival_time = "9:00"
    arrival_location = "Russian Hill"
    barbara_location = "Pacific Heights"
    barbara_available_start = "7:15"
    barbara_available_end = "22:00"
    min_meeting_duration = 60  # minutes
    travel_time_to_pacific_heights = 7  # minutes
    travel_time_to_russian_hill = 7  # minutes

    # Convert time strings to minutes since midnight
    def time_to_minutes(time_str):
        h, m = map(int, time_str.split(':'))
        return h * 60 + m

    arrival_min = time_to_minutes(arrival_time)
    barbara_start_min = time_to_minutes(barbara_available_start)
    barbara_end_min = time_to_minutes(barbara_available_end)

    # Calculate earliest possible meeting start time
    earliest_meeting_start = arrival_min + travel_time_to_pacific_heights
    if earliest_meeting_start < barbara_start_min:
        earliest_meeting_start = barbara_start_min

    # Calculate latest possible meeting end time
    latest_meeting_end = barbara_end_min
    if earliest_meeting_start + min_meeting_duration > latest_meeting_end:
        # Not enough time to meet
        itinerary = []
    else:
        # Schedule the earliest possible meeting
        meeting_start = earliest_meeting_start
        meeting_end = meeting_start + min_meeting_duration

        # Convert minutes back to time strings
        def minutes_to_time(minutes):
            h = minutes // 60
            m = minutes % 60
            return f"{h}:{m:02d}"

        itinerary = [
            {
                "action": "travel",
                "location": "Pacific Heights",
                "person": "You",
                "start_time": minutes_to_time(arrival_min),
                "end_time": minutes_to_time(arrival_min + travel_time_to_pacific_heights)
            },
            {
                "action": "meet",
                "location": "Pacific Heights",
                "person": "Barbara",
                "start_time": minutes_to_time(meeting_start),
                "end_time": minutes_to_time(meeting_end)
            },
            {
                "action": "travel",
                "location": "Russian Hill",
                "person": "You",
                "start_time": minutes_to_time(meeting_end),
                "end_time": minutes_to_time(meeting_end + travel_time_to_russian_hill)
            }
        ]

    result = {
        "itinerary": itinerary
    }
    return json.dumps(result, indent=2)

print(calculate_optimal_schedule())