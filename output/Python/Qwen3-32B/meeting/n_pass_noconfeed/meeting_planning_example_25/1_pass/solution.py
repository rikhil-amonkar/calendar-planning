import json

def time_to_minutes(time_str):
    h, m = map(int, time_str.split(':'))
    return h * 60 + m

def minutes_to_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

# Input parameters
start_location_arrival_time_str = "9:00"  # Arrival at Golden Gate Park
david_chinatown_available_start_str = "16:00"
david_chinatown_available_end_str = "21:45"
required_meeting_duration = 105  # minutes
travel_time_ggp_to_ct = 23  # minutes

# Convert to minutes
start_location_arrival_time = time_to_minutes(start_location_arrival_time_str)
david_available_start = time_to_minutes(david_chinatown_available_start_str)
david_available_end = time_to_minutes(david_chinatown_available_end_str)

# Calculate earliest possible meeting start time that allows required duration
meeting_start_candidate = david_available_start
meeting_end_candidate = meeting_start_candidate + required_meeting_duration

# Check if meeting fits within David's availability
if meeting_end_candidate <= david_available_end:
    # Check if user can travel to Chinatown in time
    required_departure_time = meeting_start_candidate - travel_time_ggp_to_ct
    if required_departure_time >= start_location_arrival_time:
        # Schedule the meeting
        itinerary = [
            {
                "action": "meet",
                "location": "Chinatown",
                "person": "David",
                "start_time": minutes_to_time(meeting_start_candidate),
                "end_time": minutes_to_time(meeting_end_candidate)
            }
        ]
        result = {"itinerary": itinerary}
        print(json.dumps(result))
    else:
        # Cannot leave in time from start location
        print(json.dumps({"itinerary": []}))
else:
    # Meeting duration not possible
    print(json.dumps({"itinerary": []}))