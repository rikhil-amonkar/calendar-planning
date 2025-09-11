import json

def minutes_to_time(m):
    hours = m // 60
    minutes = m % 60
    return f"{hours}:{minutes:02d}"

# Input parameters
travel_russian_to_richmond = 14
user_start_russian_hill = 9 * 60  # 9:00 AM in minutes
daniel_start = 19 * 60  # 7:00 PM
daniel_end = 20 * 60 + 15  # 8:15 PM
min_meeting_duration = 75

# Calculate feasible meeting start time with Daniel
latest_meeting_start = daniel_end - min_meeting_duration
meeting_start = max(daniel_start, latest_meeting_start)

# Check if meeting is possible
if (meeting_start + min_meeting_duration) <= daniel_end:
    departure_russian = meeting_start - travel_russian_to_richmond
    if departure_russian >= user_start_russian_hill:
        start_time_str = minutes_to_time(meeting_start)
        end_time_str = minutes_to_time(meeting_start + min_meeting_duration)
        itinerary = [{
            "action": "meet",
            "location": "Richmond District",
            "person": "Daniel",
            "start_time": start_time_str,
            "end_time": end_time_str
        }]
    else:
        itinerary = []
else:
    itinerary = []

result = {"itinerary": itinerary}
print(json.dumps(result, indent=2))