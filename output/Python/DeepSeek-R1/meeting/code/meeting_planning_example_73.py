from datetime import datetime, timedelta
import json

# Input parameters
user_arrival = datetime.strptime("9:00", "%H:%M")
travel_time_to_pacific = timedelta(minutes=7)
barbara_available_start = datetime.strptime("7:15", "%H:%M")
barbara_available_end = datetime.strptime("22:00", "%H:%M")
min_meeting = 60

# Calculate earliest possible arrival at Pacific Heights
earliest_arrival = user_arrival + travel_time_to_pacific
meeting_start = max(earliest_arrival, barbara_available_start)
meeting_end = barbara_available_end

# Check if meeting duration meets minimum requirement
duration = (meeting_end - meeting_start).total_seconds() // 60
itinerary = []
if duration >= min_meeting:
    start_time = f"{meeting_start.hour}:{meeting_start.minute:02d}"
    end_time = f"{meeting_end.hour}:{meeting_end.minute:02d}"
    itinerary.append({
        "action": "meet",
        "location": "Pacific Heights",
        "person": "Barbara",
        "start_time": start_time,
        "end_time": end_time
    })

print(json.dumps({"itinerary": itinerary}))