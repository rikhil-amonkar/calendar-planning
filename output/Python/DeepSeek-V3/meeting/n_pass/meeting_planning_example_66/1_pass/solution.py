import json

def calculate_optimal_schedule():
    # Input parameters
    arrival_time = "9:00"
    robert_available_start = "11:15"
    robert_available_end = "17:45"
    min_meeting_duration = 120  # minutes
    travel_nob_to_presidio = 17  # minutes
    travel_presidio_to_nob = 18  # minutes

    # Convert time strings to minutes since midnight
    def time_to_minutes(time_str):
        h, m = map(int, time_str.split(':'))
        return h * 60 + m

    arrival_min = time_to_minutes(arrival_time)
    robert_start_min = time_to_minutes(robert_available_start)
    robert_end_min = time_to_minutes(robert_available_end)

    # Calculate earliest possible meeting start time
    # Leave Nob Hill at arrival_time, arrive at Presidio at arrival_time + travel time
    earliest_arrival_presidio = arrival_min + travel_nob_to_presidio
    meeting_start = max(earliest_arrival_presidio, robert_start_min)
    meeting_end = meeting_start + min_meeting_duration

    # Check if meeting fits within Robert's availability
    if meeting_end > robert_end_min:
        # Try to start earlier if possible
        meeting_start = robert_end_min - min_meeting_duration
        if meeting_start < robert_start_min:
            meeting_start = robert_start_min
            meeting_end = robert_end_min
            if meeting_end - meeting_start < min_meeting_duration:
                # Cannot meet for required duration
                return {"itinerary": []}

    # Calculate return time
    return_departure = meeting_end
    return_arrival = return_departure + travel_presidio_to_nob

    # Convert minutes back to time strings
    def minutes_to_time(m):
        h = m // 60
        m = m % 60
        return f"{h}:{m:02d}"

    itinerary = [
        {
            "action": "travel",
            "location": "Presidio",
            "person": "self",
            "start_time": minutes_to_time(arrival_min),
            "end_time": minutes_to_time(earliest_arrival_presidio)
        },
        {
            "action": "meet",
            "location": "Presidio",
            "person": "Robert",
            "start_time": minutes_to_time(meeting_start),
            "end_time": minutes_to_time(meeting_end)
        },
        {
            "action": "travel",
            "location": "Nob Hill",
            "person": "self",
            "start_time": minutes_to_time(return_departure),
            "end_time": minutes_to_time(return_arrival)
        }
    ]

    return {"itinerary": itinerary}

# Compute and output the schedule
schedule = calculate_optimal_schedule()
print(json.dumps(schedule, indent=2))