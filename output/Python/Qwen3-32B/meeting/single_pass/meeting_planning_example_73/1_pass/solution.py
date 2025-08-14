import json

def time_to_str(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

# Input parameters
travel_time_russian_to_pacific = 7
barbara_start_time_minutes = 7 * 60 + 15  # 7:15 AM
barbara_end_time_minutes = 22 * 60 + 0    # 10:00 PM
minimum_meeting_duration = 60
user_arrival_russian_hill_minutes = 9 * 60 + 0  # 9:00 AM

# Compute arrival at Pacific Heights
arrival_pacific_minutes = user_arrival_russian_hill_minutes + travel_time_russian_to_pacific

# Compute meeting end time
meeting_end_minutes = arrival_pacific_minutes + minimum_meeting_duration

# Check if the meeting is within Barbara's availability
if (arrival_pacific_minutes >= barbara_start_time_minutes and
    meeting_end_minutes <= barbara_end_time_minutes):
    itinerary = [
        {
            "action": "meet",
            "location": "Pacific Heights",
            "person": "Barbara",
            "start_time": time_to_str(arrival_pacific_minutes),
            "end_time": time_to_str(meeting_end_minutes)
        }
    ]
else:
    itinerary = []

result = {"itinerary": itinerary}
print(json.dumps(result, indent=2))