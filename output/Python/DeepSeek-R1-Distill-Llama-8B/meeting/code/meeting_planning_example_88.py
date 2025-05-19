# Define the travel times as a dictionary
travel_times = {
    "Sunset District": {
        "Golden Gate Park": 11,
    },
    "Golden Gate Park": {
        "Sunset District": 10,
    }
}

# Starting location and time
start_location = "Sunset District"
start_time = "9:00"

itinerary = []

def calculate_travel_time(from_loc, to_loc):
    return travel_times[from_loc][to_loc]

def is_available(person):
    return True

def schedule_meeting(current_loc, person):
    if not is_available(person):
        return False
    # Calculate arrival time
    arrival_time = add_time(current_loc, start_time)
    # Check if arrival time is before the person's start time
    if arrival_time >= person["start"]:
        return False
    # Calculate meeting end time
    meeting_end = add_time(current_loc, start_time, person["duration"])
    itinerary.append({
        "action": "meet",
        "location": person["location"],
        "person": person["name"],
        "start_time": arrival_time,
        "end_time": meeting_end
    })
    # Update current location and time
    current_loc = person["location"]
    current_time = meeting_end
    return True

# Helper function to add time
def add_time(location, current_time, duration=0):
    hours, minutes = map(int, current_time.split(":"))
    total_minutes = minutes + duration
    hours += total_minutes // 60
    minutes = total_minutes % 60
    return f"{hours:02d}:{minutes:02d}"

# Meeting Joshua
meeting_joshua = {
    "name": "Joshua",
    "location": "Golden Gate Park",
    "start": "8:45",
    "end": "9:45",
    "duration": 15
}
if schedule_meeting(start_location, meeting_joshua):
    pass

# Convert itinerary to JSON format
import json
itinerary_json = [
    {
        "action": "meet",
        "location": meeting_joshua["location"],
        "person": meeting_joshua["name"],
        "start_time": meeting_joshua["start"],
        "end_time": meeting_joshua["end"]
    }
]

# Remove duplicates and sort by time
unique_itinerary = []
for meeting in itinerary:
    if not any(m["person"] == meeting["person"] for m in unique_itinerary):
        unique_itinerary.append(meeting)

# Sort the itinerary by start time
unique_itinerary.sort(key=lambda x: (x['start_time'], x['end_time']))

# Convert to JSON
final_itinerary = [
    {
        "action": "meet",
        "location": m["location"],
        "person": m["person"],
        "start_time": m["start_time"],
        "end_time": m["end_time"]
    }
    for m in unique_itinerary
]

# Output the JSON
print(json.dumps(final_itinerary))