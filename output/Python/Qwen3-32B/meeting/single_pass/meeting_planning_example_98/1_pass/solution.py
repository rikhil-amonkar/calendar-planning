import json

def time_to_minutes(time_str):
    h, m = map(int, time_str.split(':'))
    return h * 60 + m

def minutes_to_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m}"

# Parameters
user_start_location = "Alamo Square"
user_arrival_time_str = "9:00"

# Timothy's constraints
timothy_location = "Richmond District"
timothy_available_start_str = "20:45"
timothy_available_end_str = "21:30"
timothy_min_duration = 45  # minutes

# Travel time from user's start location to timothy's location
travel_time_minutes = 12  # Alamo Square to Richmond District

# Convert times to minutes
user_arrival_time = time_to_minutes(user_arrival_time_str)
timothy_available_start = time_to_minutes(timothy_available_start_str)
timothy_available_end = time_to_minutes(timothy_available_end_str)

# Calculate latest possible start time for meeting
latest_meeting_start = timothy_available_end - timothy_min_duration

# Check if latest_meeting_start is within Timothy's availability
if latest_meeting_start >= timothy_available_start:
    # Calculate required departure time from user's location
    required_departure = latest_meeting_start - travel_time_minutes
    # Check if departure is possible (after user's arrival)
    if required_departure >= user_arrival_time:
        # Meeting is possible
        meeting_start_str = minutes_to_time(latest_meeting_start)
        meeting_end_str = minutes_to_time(latest_meeting_start + timothy_min_duration)
        itinerary = [
            {
                "action": "meet",
                "location": timothy_location,
                "person": "Timothy",
                "start_time": meeting_start_str,
                "end_time": meeting_end_str
            }
        ]
    else:
        # Departure not possible, no meeting
        itinerary = []
else:
    # Meeting duration not possible
    itinerary = []

# Output as JSON
result = {"itinerary": itinerary}
print(json.dumps(result, indent=2))