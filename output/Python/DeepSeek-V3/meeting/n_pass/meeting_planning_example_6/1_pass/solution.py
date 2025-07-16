import json

def calculate_optimal_schedule():
    # Input parameters
    arrival_time = "9:00"
    arrival_location = "Fisherman's Wharf"
    kenneth_available_start = "14:15"
    kenneth_available_end = "19:45"
    meeting_duration = 90  # minutes
    travel_time_fw_to_nh = 11  # minutes
    travel_time_nh_to_fw = 11  # minutes

    # Convert time strings to minutes since midnight for easier calculations
    def time_to_minutes(time_str):
        h, m = map(int, time_str.split(':'))
        return h * 60 + m

    arrival_min = time_to_minutes(arrival_time)
    kenneth_start_min = time_to_minutes(kenneth_available_start)
    kenneth_end_min = time_to_minutes(kenneth_available_end)

    # Calculate the earliest possible meeting start time
    # You need to travel from Fisherman's Wharf to Nob Hill to meet Kenneth
    earliest_departure = arrival_min  # can leave immediately
    earliest_arrival_nh = earliest_departure + travel_time_fw_to_nh
    meeting_start = max(earliest_arrival_nh, kenneth_start_min)
    meeting_end = meeting_start + meeting_duration

    # Check if the meeting fits within Kenneth's availability
    if meeting_end > kenneth_end_min:
        # Not enough time to meet, adjust meeting start to fit
        meeting_start = kenneth_end_min - meeting_duration
        meeting_end = kenneth_end_min

    # Check if meeting is possible at all
    if meeting_start < kenneth_start_min or meeting_end > kenneth_end_min:
        return {"itinerary": []}

    # Convert back to time strings
    def minutes_to_time(minutes):
        h = minutes // 60
        m = minutes % 60
        return f"{h}:{m:02d}"

    itinerary = [
        {
            "action": "travel",
            "location": "Nob Hill",
            "person": "self",
            "start_time": minutes_to_time(earliest_departure),
            "end_time": minutes_to_time(earliest_arrival_nh)
        },
        {
            "action": "meet",
            "location": "Nob Hill",
            "person": "Kenneth",
            "start_time": minutes_to_time(meeting_start),
            "end_time": minutes_to_time(meeting_end)
        }
    ]

    return {"itinerary": itinerary}

result = calculate_optimal_schedule()
print(json.dumps(result, indent=2))