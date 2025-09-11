import json

def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

# Input parameters
user_start_time = 9 * 60  # 9:00 AM in minutes
joshua_start = 20 * 60 + 45  # 8:45 PM
joshua_end = 21 * 60 + 45  # 9:45 PM
travel_time_sun_to_ggp = 11  # minutes
min_meeting_duration = 15  # minutes

# Calculate latest arrival time at GGP to allow 15 min meeting
latest_arrival_ggp = joshua_end - min_meeting_duration

# Calculate departure time from Sunset District
departure_time = latest_arrival_ggp - travel_time_sun_to_ggp

itinerary = []

# Check if departure is possible (after arrival at Sunset District)
if departure_time >= user_start_time:
    arrival_time_ggp = departure_time + travel_time_sun_to_ggp
    meeting_start = max(arrival_time_ggp, joshua_start)
    meeting_end = meeting_start + min_meeting_duration
    
    # Verify meeting fits within Joshua's availability window
    if meeting_end <= joshua_end:
        itinerary = [{
            "action": "meet",
            "location": "Golden Gate Park",
            "person": "Joshua",
            "start_time": minutes_to_time(meeting_start),
            "end_time": minutes_to_time(meeting_end)
        }]

# Output JSON
result = {"itinerary": itinerary}
print(json.dumps(result, indent=2))