# Define the travel times as a dictionary
travel_times = {
    "Presidio": {
        "Golden Gate Park": 12,
        "Bayview": 31,
        "Chinatown": 21,
        "North Beach": 18,
        "Mission District": 26,
    },
    "Golden Gate Park": {
        "Presidio": 11,
        "Bayview": 23,
        "Chinatown": 23,
        "North Beach": 24,
        "Mission District": 17,
    },
    "Bayview": {
        "Presidio": 31,
        "Golden Gate Park": 22,
        "Chinatown": 18,
        "North Beach": 21,
        "Mission District": 13,
    },
    "Chinatown": {
        "Presidio": 19,
        "Golden Gate Park": 23,
        "Bayview": 22,
        "North Beach": 3,
        "Mission District": 18,
    },
    "North Beach": {
        "Presidio": 17,
        "Golden Gate Park": 22,
        "Bayview": 22,
        "Chinatown": 6,
        "Mission District": 18,
    },
    "Mission District": {
        "Presidio": 25,
        "Golden Gate Park": 17,
        "Bayview": 15,
        "Chinatown": 16,
        "North Beach": 17,
    }
}

# Starting location and time
start_location = "Presidio"
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

# Meeting Ronald
meeting_ronald = {
    "name": "Ronald",
    "location": "Chinatown",
    "start": "7:15",
    "end": "2:45",
    "duration": 90
}
if schedule_meeting(start_location, meeting_ronald):
    pass

# Meeting Daniel
meeting_daniel = {
    "name": "Daniel",
    "location": "Mission District",
    "start": "7:00",
    "end": "11:15",
    "duration": 105
}
if schedule_meeting("Chinatown", meeting_daniel):
    pass

# Meeting William
meeting_william = {
    "name": "William",
    "location": "North Beach",
    "start": "1:15",
    "end": "8:15",
    "duration": 15
}
if schedule_meeting("Mission District", meeting_william):
    pass

# Meeting Jessica
meeting_jessica = {
    "name": "Jessica",
    "location": "Golden Gate Park",
    "start": "1:45",
    "end": "3:00",
    "duration": 30
}
if schedule_meeting("North Beach", meeting_jessica):
    pass

# Meeting Ashley
meeting_ashley = {
    "name": "Ashley",
    "location": "Bayview",
    "start": "5:15",
    "end": "8:00",
    "duration": 105
}
if schedule_meeting("Golden Gate Park", meeting_ashley):
    pass

# Convert itinerary to JSON format
import json
itinerary_json = [
    {
        "action": "meet",
        "location": meeting_ronald["location"],
        "person": meeting_ronald["name"],
        "start_time": meeting_ronald["start"],
        "end_time": meeting_ronald["end"]
    },
    {
        "action": "meet",
        "location": meeting_daniel["location"],
        "person": meeting_daniel["name"],
        "start_time": meeting_daniel["start"],
        "end_time": meeting_daniel["end"]
    },
    {
        "action": "meet",
        "location": meeting_william["location"],
        "person": meeting_william["name"],
        "start_time": meeting_william["start"],
        "end_time": meeting_william["end"]
    },
    {
        "action": "meet",
        "location": meeting_jessica["location"],
        "person": meeting_jessica["name"],
        "start_time": meeting_jessica["start"],
        "end_time": meeting_jessica["end"]
    },
    {
        "action": "meet",
        "location": meeting_ashley["location"],
        "person": meeting_ashley["name"],
        "start_time": meeting_ashley["start"],
        "end_time": meeting_ashley["end"]
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