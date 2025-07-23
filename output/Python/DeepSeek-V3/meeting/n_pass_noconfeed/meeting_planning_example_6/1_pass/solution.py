import json

def calculate_optimal_schedule():
    # Input parameters
    arrival_time = "9:00"
    arrival_location = "Fisherman's Wharf"
    kenneth_location = "Nob Hill"
    kenneth_available_start = "14:15"
    kenneth_available_end = "19:45"
    min_meeting_duration = 90  # minutes
    travel_time_fw_to_nh = 11  # minutes
    travel_time_nh_to_fw = 11  # minutes

    # Convert time strings to minutes since midnight
    def time_to_minutes(time_str):
        h, m = map(int, time_str.split(':'))
        return h * 60 + m

    arrival_min = time_to_minutes(arrival_time)
    kenneth_start_min = time_to_minutes(kenneth_available_start)
    kenneth_end_min = time_to_minutes(kenneth_available_end)

    # Calculate possible meeting window
    # Earliest you can arrive at Nob Hill is arrival_time + travel_time_fw_to_nh
    earliest_arrival_nh = arrival_min + travel_time_fw_to_nh
    # Latest you can leave Nob Hill is kenneth_end_min - travel_time_nh_to_fw
    latest_departure_nh = kenneth_end_min - travel_time_nh_to_fw

    # Meeting must be at least min_meeting_duration and within Kenneth's availability
    meeting_start = max(earliest_arrival_nh, kenneth_start_min)
    meeting_end = min(meeting_start + min_meeting_duration, latest_departure_nh)

    # Check if meeting is possible
    if meeting_end - meeting_start >= min_meeting_duration:
        # Convert minutes back to time strings
        def minutes_to_time(minutes):
            h = minutes // 60
            m = minutes % 60
            return f"{h}:{m:02d}"

        travel_to_start = minutes_to_time(meeting_start - travel_time_fw_to_nh)
        travel_to_end = minutes_to_time(meeting_end + travel_time_nh_to_fw)

        itinerary = [
            {
                "action": "travel",
                "location": "Fisherman's Wharf to Nob Hill",
                "person": "You",
                "start_time": travel_to_start,
                "end_time": minutes_to_time(meeting_start)
            },
            {
                "action": "meet",
                "location": kenneth_location,
                "person": "Kenneth",
                "start_time": minutes_to_time(meeting_start),
                "end_time": minutes_to_time(meeting_end)
            },
            {
                "action": "travel",
                "location": "Nob Hill to Fisherman's Wharf",
                "person": "You",
                "start_time": minutes_to_time(meeting_end),
                "end_time": travel_to_end
            }
        ]
    else:
        itinerary = []

    # Output as JSON
    result = {
        "itinerary": itinerary
    }
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    calculate_optimal_schedule()