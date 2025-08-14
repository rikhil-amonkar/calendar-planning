import json

def minutes_to_time_str(minutes):
    hours = minutes // 60
    minutes_part = minutes % 60
    return f"{hours}:{minutes_part:02d}"

# Input parameters
arrival_russian_hill_minutes = 9 * 60  # 9:00 AM
barbara_start_time_minutes = 13 * 60 + 15  # 1:15 PM
barbara_end_time_minutes = 18 * 60 + 15  # 6:15 PM
min_meeting_duration = 45  # minutes
travel_time_russian_to_richmond = 14  # minutes

# Calculate earliest possible meeting start with Barbara
meeting_start = barbara_start_time_minutes
meeting_end = meeting_start + min_meeting_duration

# Check if meeting fits within Barbara's availability
if meeting_end <= barbara_end_time_minutes:
    # Check if user can arrive at Richmond in time for the meeting
    required_departure_russian = meeting_start - travel_time_russian_to_richmond
    if required_departure_russian >= arrival_russian_hill_minutes:
        # Schedule the meeting
        itinerary = [
            {
                "action": "meet",
                "location": "Richmond District",
                "person": "Barbara",
                "start_time": minutes_to_time_str(meeting_start),
                "end_time": minutes_to_time_str(meeting_end)
            }
        ]
        result = {"itinerary": itinerary}
        print(json.dumps(result, indent=2))
    else:
        # Cannot reach in time, no meeting
        print(json.dumps({"itinerary": []}))
else:
    # Not enough time for the meeting
    print(json.dumps({"itinerary": []}))