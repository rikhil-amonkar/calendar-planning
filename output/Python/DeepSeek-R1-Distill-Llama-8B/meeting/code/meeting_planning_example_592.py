# Define the travel times as a dictionary
travel_times = {
    "North Beach": {
        "Pacific Heights": 8,
        "Chinatown": 6,
        "Union Square": 7,
        "Mission District": 18,
        "Golden Gate Park": 22,
        "Nob Hill": 7,
    },
    "Pacific Heights": {
        "North Beach": 9,
        "Chinatown": 11,
        "Union Square": 12,
        "Mission District": 15,
        "Golden Gate Park": 15,
        "Nob Hill": 8,
    },
    "Chinatown": {
        "North Beach": 3,
        "Pacific Heights": 10,
        "Union Square": 7,
        "Mission District": 18,
        "Golden Gate Park": 23,
        "Nob Hill": 8,
    },
    "Union Square": {
        "North Beach": 10,
        "Pacific Heights": 15,
        "Chinatown": 7,
        "Mission District": 14,
        "Golden Gate Park": 22,
        "Nob Hill": 9,
    },
    "Mission District": {
        "North Beach": 17,
        "Pacific Heights": 16,
        "Chinatown": 16,
        "Union Square": 15,
        "Golden Gate Park": 17,
        "Nob Hill": 12,
    },
    "Golden Gate Park": {
        "North Beach": 24,
        "Pacific Heights": 16,
        "Chinatown": 23,
        "Union Square": 22,
        "Mission District": 17,
        "Nob Hill": 20,
    },
    "Nob Hill": {
        "North Beach": 8,
        "Pacific Heights": 8,
        "Chinatown": 6,
        "Union Square": 7,
        "Mission District": 13,
        "Golden Gate Park": 17,
    }
}

# Starting location and time
start_location = "North Beach"
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

# Meeting James
meeting_james = {
    "name": "James",
    "location": "Pacific Heights",
    "start": "8:00",
    "end": "10:00",
    "duration": 120
}
if schedule_meeting(start_location, meeting_james):
    pass

# Meeting Robert
meeting_robert = {
    "name": "Robert",
    "location": "Chinatown",
    "start": "12:15",
    "end": "4:45",
    "duration": 90
}
if schedule_meeting("Pacific Heights", meeting_robert):
    pass

# Meeting Jeffrey
meeting_jeffrey = {
    "name": "Jeffrey",
    "location": "Union Square",
    "start": "9:30",
    "end": "3:30",
    "duration": 120
}
if schedule_meeting("Nob Hill", meeting_jeffrey):
    pass

# Meeting Carol
meeting_carol = {
    "name": "Carol",
    "location": "Mission District",
    "start": "6:15",
    "end": "9:15",
    "duration": 15
}
if schedule_meeting("Union Square", meeting_carol):
    pass

# Meeting Mark
meeting_mark = {
    "name": "Mark",
    "location": "Golden Gate Park",
    "start": "11:30",
    "end": "5:45",
    "duration": 15
}
if schedule_meeting("Mission District", meeting_mark):
    pass

# Meeting Sandra
meeting_sandra = {
    "name": "Sandra",
    "location": "Nob Hill",
    "start": "8:00",
    "end": "3:30",
    "duration": 15
}
if schedule_meeting("Golden Gate Park", meeting_sandra):
    pass

# Convert itinerary to JSON format
import json
itinerary_json = [
    {
        "action": "meet",
        "location": meeting_james["location"],
        "person": meeting_james["name"],
        "start_time": meeting_james["start"],
        "end_time": meeting_james["end"]
    },
    {
        "action": "meet",
        "location": meeting_robert["location"],
        "person": meeting_robert["name"],
        "start_time": meeting_robert["start"],
        "end_time": meeting_robert["end"]
    },
    {
        "action": "meet",
        "location": meeting_jeffrey["location"],
        "person": meeting_jeffrey["name"],
        "start_time": meeting_jeffrey["start"],
        "end_time": meeting_jeffrey["end"]
    },
    {
        "action": "meet",
        "location": meeting_carol["location"],
        "person": meeting_carol["name"],
        "start_time": meeting_carol["start"],
        "end_time": meeting_carol["end"]
    },
    {
        "action": "meet",
        "location": meeting_mark["location"],
        "person": meeting_mark["name"],
        "start_time": meeting_mark["start"],
        "end_time": meeting_mark["end"]
    },
    {
        "action": "meet",
        "location": meeting_sandra["location"],
        "person": meeting_sandra["name"],
        "start_time": meeting_sandra["start"],
        "end_time": meeting_sandra["end"]
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