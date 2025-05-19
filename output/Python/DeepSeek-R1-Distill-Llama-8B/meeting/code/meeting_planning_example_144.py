# Define the travel times as a dictionary
travel_times = {
    "The Castro": {
        "Mission District": 7,
        "Financial District": 20
    },
    "Mission District": {
        "The Castro": 7,
        "Financial District": 17
    },
    "Financial District": {
        "The Castro": 20,
        "Mission District": 17
    }
}

# Starting location and time
start_location = "The Castro"
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

# Meeting Laura
meeting_laura = {
    "name": "Laura",
    "location": "Mission District",
    "start": "12:15",
    "end": "7:45",
    "duration": 75
}
if schedule_meeting(start_location, meeting_laura):
    pass

# Meeting Anthony
meeting_anthony = {
    "name": "Anthony",
    "location": "Financial District",
    "start": "12:30",
    "end": "2:45",
    "duration": 30
}
if schedule_meeting("Mission District", meeting_anthony):
    pass

# Convert itinerary to JSON format
import json
itinerary_json = [
    {
        "action": "meet",
        "location": meeting_laura["location"],
        "person": meeting_laura["name"],
        "start_time": meeting_laura["start"],
        "end_time": meeting_laura["end"]
    },
    {
        "action": "meet",
        "location": meeting_anthony["location"],
        "person": meeting_anthony["name"],
        "start_time": meeting_anthony["start"],
        "end_time": meeting_anthony["end"]
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