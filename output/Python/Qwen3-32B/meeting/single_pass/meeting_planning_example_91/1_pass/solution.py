import json

def to_time_str(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

# Input parameters
arrival_russian_hill = 9 * 60  # 9:00 AM in minutes
daniel_start = 19 * 60  # 7:00 PM
daniel_end = 20 * 60 + 15  # 8:15 PM
min_meeting_duration = 75  # minutes
travel_russian_to_richmond = 14  # minutes

# Calculate possible meeting time with Daniel
latest_meeting_start = daniel_end - min_meeting_duration
itinerary = []

if daniel_start <= latest_meeting_start:
    meeting_start = daniel_start
    meeting_end = meeting_start + min_meeting_duration
    
    if meeting_end <= daniel_end:
        required_departure = meeting_start - travel_russian_to_richmond
        if required_departure >= arrival_russian_hill:
            itinerary = [{
                "action": "meet",
                "location": "Richmond District",
                "person": "Daniel",
                "start_time": to_time_str(meeting_start),
                "end_time": to_time_str(meeting_end)
            }]

result = {"itinerary": itinerary}
print(json.dumps(result, indent=2))