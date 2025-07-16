import json

def compute_optimal_schedule():
    # Input parameters
    arrival_location = "Russian Hill"
    arrival_time = "9:00"
    barbara_location = "Richmond District"
    barbara_available_start = "13:15"
    barbara_available_end = "18:15"
    min_meeting_duration = 45  # minutes
    travel_time_to_richmond = 14  # minutes
    travel_time_back = 13  # minutes

    # Convert time strings to minutes since midnight for easier calculations
    def time_to_minutes(time_str):
        h, m = map(int, time_str.split(':'))
        return h * 60 + m

    arrival_min = time_to_minutes(arrival_time)
    barbara_start_min = time_to_minutes(barbara_available_start)
    barbara_end_min = time_to_minutes(barbara_available_end)

    # Calculate the earliest possible meeting start time
    # You need to travel from Russian Hill to Richmond District
    earliest_departure = arrival_min  # can leave immediately
    earliest_arrival_at_richmond = earliest_departure + travel_time_to_richmond
    meeting_start = max(earliest_arrival_at_richmond, barbara_start_min)
    
    # Calculate the latest possible meeting end time
    # You need to travel back to Russian Hill after the meeting
    latest_departure_from_richmond = barbara_end_min
    latest_meeting_end = latest_departure_from_richmond
    meeting_end = meeting_start + min_meeting_duration

    if meeting_end > latest_meeting_end:
        # No feasible meeting time
        itinerary = []
    else:
        # Convert back to time strings
        def minutes_to_time(minutes):
            h = minutes // 60
            m = minutes % 60
            return f"{h}:{m:02d}"

        itinerary = [
            {
                "action": "travel",
                "location": "Richmond District",
                "person": "self",
                "start_time": minutes_to_time(earliest_departure),
                "end_time": minutes_to_time(earliest_arrival_at_richmond)
            },
            {
                "action": "meet",
                "location": "Richmond District",
                "person": "Barbara",
                "start_time": minutes_to_time(meeting_start),
                "end_time": minutes_to_time(meeting_end)
            },
            {
                "action": "travel",
                "location": "Russian Hill",
                "person": "self",
                "start_time": minutes_to_time(meeting_end),
                "end_time": minutes_to_time(meeting_end + travel_time_back)
            }
        ]

    # Output the result as JSON
    result = {
        "itinerary": itinerary
    }
    print(json.dumps(result, indent=2))

compute_optimal_schedule()