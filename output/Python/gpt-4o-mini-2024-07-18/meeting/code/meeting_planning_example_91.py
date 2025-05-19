import json
from datetime import datetime, timedelta

# Define the meeting constraints and travel distances
arrive_time_russian_hill = datetime.strptime("09:00", "%H:%M")
travel_time_russian_to_richmond = 14  # in minutes
travel_time_richmond_to_russian = 13  # in minutes
daniel_avail_start = datetime.strptime("19:00", "%H:%M")
daniel_avail_end = datetime.strptime("20:15", "%H:%M")
meeting_duration = timedelta(minutes=75)

# Calculate the optimal meeting schedule
itinerary = []
current_time = arrive_time_russian_hill

# Meeting with Daniel at Richmond District
# Calculate the time we need to leave Russian Hill to meet Daniel
latest_departure_from_richmond = daniel_avail_end - meeting_duration

# Determine the latest time we can leave Russian Hill
if latest_departure_from_richmond < arrive_time_russian_hill:
    # If current time is already past the latest departure, we cannot meet Daniel
    print(json.dumps({"itinerary": []}))
    exit()

# Ensure we have time to meet Daniel
current_time = latest_departure_from_richmond - timedelta(minutes=travel_time_russian_to_richmond)

# Schedule meeting with Daniel
meet_start_time = latest_departure_from_richmond - meeting_duration
meet_end_time = latest_departure_from_richmond

itinerary.append({
    "action": "meet",
    "location": "Richmond District",
    "person": "Daniel",
    "start_time": meet_start_time.strftime("%H:%M"),
    "end_time": meet_end_time.strftime("%H:%M")
})

# Return JSON output
output = {
    "itinerary": itinerary
}

print(json.dumps(output, indent=2))