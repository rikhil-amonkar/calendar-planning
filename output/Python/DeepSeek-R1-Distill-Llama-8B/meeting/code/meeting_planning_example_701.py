# Define the travel times as a dictionary
travel_times = {
    # From Mission District
    "Mission District": {
        "The Castro": 7,
        "Nob Hill": 12,
        "Presidio": 25,
        "Marina District": 19,
        "Pacific Heights": 16,
        "Golden Gate Park": 17,
        "Chinatown": 16,
        "Richmond District": 20,
    },
    # From The Castro
    "The Castro": {
        "Mission District": 7,
        "Nob Hill": 16,
        "Presidio": 20,
        "Marina District": 21,
        "Pacific Heights": 16,
        "Golden Gate Park": 11,
        "Chinatown": 22,
        "Richmond District": 16,
    },
    # From Nob Hill
    "Nob Hill": {
        "Mission District": 13,
        "The Castro": 17,
        "Presidio": 17,
        "Marina District": 11,
        "Pacific Heights": 8,
        "Golden Gate Park": 17,
        "Chinatown": 6,
        "Richmond District": 14,
    },
    # From Presidio
    "Presidio": {
        "Mission District": 26,
        "The Castro": 21,
        "Nob Hill": 18,
        "Marina District": 11,
        "Pacific Heights": 11,
        "Golden Gate Park": 12,
        "Chinatown": 21,
        "Richmond District": 7,
    },
    # From Marina District
    "Marina District": {
        "Mission District": 20,
        "The Castro": 22,
        "Nob Hill": 12,
        "Presidio": 10,
        "Pacific Heights": 6,
        "Golden Gate Park": 18,
        "Chinatown": 15,
        "Richmond District": 11,
    },
    # From Pacific Heights
    "Pacific Heights": {
        "Mission District": 15,
        "The Castro": 16,
        "Nob Hill": 8,
        "Presidio": 11,
        "Marina District": 6,
        "Golden Gate Park": 15,
        "Chinatown": 11,
        "Richmond District": 12,
    },
    # From Golden Gate Park
    "Golden Gate Park": {
        "Mission District": 17,
        "The Castro": 13,
        "Nob Hill": 20,
        "Presidio": 11,
        "Marina District": 16,
        "Pacific Heights": 16,
        "Chinatown": 23,
        "Richmond District": 7,
    },
    # From Chinatown
    "Chinatown": {
        "Mission District": 17,
        "The Castro": 22,
        "Nob Hill": 9,
        "Presidio": 19,
        "Marina District": 12,
        "Pacific Heights": 10,
        "Golden Gate Park": 23,
        "Richmond District": 20,
    },
    # From Richmond District
    "Richmond District": {
        "Mission District": 20,
        "The Castro": 16,
        "Nob Hill": 17,
        "Presidio": 7,
        "Marina District": 9,
        "Pacific Heights": 10,
        "Golden Gate Park": 9,
        "Chinatown": 20,
    },
}

# Define the availability as a dictionary
availability = {
    "Daniel": {"start": "8:15", "end": "11:00", "duration": 15},
    "Lisa": {"start": "7:15", "end": "9:15", "duration": 120},
    "Elizabeth": {"start": "9:15", "end": "10:15", "duration": 45},
    "Steven": {"start": "4:30", "end": "8:45", "duration": 90},
    "Timothy": {"start": "12:00", "end": "6:00", "duration": 90},
    "Ashley": {"start": "8:45", "end": "9:45", "duration": 60},
    "Kevin": {"start": "12:00", "end": "7:00", "duration": 30},
    "Betty": {"start": "1:15", "end": "3:45", "duration": 30},
}

# Starting location and time
start_location = "Mission District"
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

# Meeting Daniel
meeting_daniel = {
    "name": "Daniel",
    "location": "Nob Hill",
    "start": "8:15",
    "end": "11:00",
    "duration": 15
}
if schedule_meeting(start_location, meeting_daniel):
    pass

# Meeting Kevin
meeting_kevin = {
    "name": "Kevin",
    "location": "Chinatown",
    "start": "12:00",
    "end": "7:00",
    "duration": 30
}
if schedule_meeting("Nob Hill", meeting_kevin):
    pass

# Meeting Timothy
meeting_timothy = {
    "name": "Timothy",
    "location": "Pacific Heights",
    "start": "12:00",
    "end": "6:00",
    "duration": 90
}
if schedule_meeting("Chinatown", meeting_timothy):
    pass

# Meeting Steven
meeting_steven = {
    "name": "Steven",
    "location": "Marina District",
    "start": "4:30",
    "end": "8:45",
    "duration": 90
}
if schedule_meeting("Pacific Heights", meeting_steven):
    pass

# Meeting Lisa
meeting_lisa = {
    "name": "Lisa",
    "location": "The Castro",
    "start": "7:15",
    "end": "9:15",
    "duration": 120
}
if schedule_meeting("Marina District", meeting_lisa):
    pass

# Meeting Elizabeth
meeting_elizabeth = {
    "name": "Elizabeth",
    "location": "Presidio",
    "start": "9:15",
    "end": "10:15",
    "duration": 45
}
if schedule_meeting("The Castro", meeting_elizabeth):
    pass

# Meeting Ashley
meeting_ashley = {
    "name": "Ashley",
    "location": "Golden Gate Park",
    "start": "8:45",
    "end": "9:45",
    "duration": 60
}
if schedule_meeting("Presidio", meeting_ashley):
    pass

# Meeting Betty
meeting_betty = {
    "name": "Betty",
    "location": "Richmond District",
    "start": "1:15",
    "end": "3:45",
    "duration": 30
}
if schedule_meeting("Golden Gate Park", meeting_betty):
    pass

# Convert itinerary to JSON format
import json
itinerary_json = [
    {
        "action": "meet",
        "location": meeting_daniel["location"],
        "person": meeting_daniel["name"],
        "start_time": meeting_daniel["start"],
        "end_time": meeting_daniel["end"]
    },
    {
        "action": "meet",
        "location": meeting_kevin["location"],
        "person": meeting_kevin["name"],
        "start_time": meeting_kevin["start"],
        "end_time": meeting_kevin["end"]
    },
    {
        "action": "meet",
        "location": meeting_timothy["location"],
        "person": meeting_timothy["name"],
        "start_time": meeting_timothy["start"],
        "end_time": meeting_timothy["end"]
    },
    {
        "action": "meet",
        "location": meeting_steven["location"],
        "person": meeting_steven["name"],
        "start_time": meeting_steven["start"],
        "end_time": meeting_steven["end"]
    },
    {
        "action": "meet",
        "location": meeting_lisa["location"],
        "person": meeting_lisa["name"],
        "start_time": meeting_lisa["start"],
        "end_time": meeting_lisa["end"]
    },
    {
        "action": "meet",
        "location": meeting_elizabeth["location"],
        "person": meeting_elizabeth["name"],
        "start_time": meeting_elizabeth["start"],
        "end_time": meeting_elizabeth["end"]
    },
    {
        "action": "meet",
        "location": meeting_ashley["location"],
        "person": meeting_ashley["name"],
        "start_time": meeting_ashley["start"],
        "end_time": meeting_ashley["end"]
    },
    {
        "action": "meet",
        "location": meeting_betty["location"],
        "person": meeting_betty["name"],
        "start_time": meeting_betty["start"],
        "end_time": meeting_betty["end"]
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