import json
from datetime import datetime, timedelta

# Define travel times (in minutes) between locations
travel_times = {
    ("Russian Hill", "Pacific Heights"): 7,
    ("Russian Hill", "North Beach"): 5,
    ("Russian Hill", "Golden Gate Park"): 21,
    ("Russian Hill", "Embarcadero"): 8,
    ("Russian Hill", "Haight-Ashbury"): 17,
    ("Russian Hill", "Fisherman's Wharf"): 7,
    ("Russian Hill", "Mission District"): 16,
    ("Russian Hill", "Alamo Square"): 15,
    ("Russian Hill", "Bayview"): 23,
    ("Russian Hill", "Richmond District"): 14,
    ("Pacific Heights", "North Beach"): 9,
    ("Pacific Heights", "Golden Gate Park"): 15,
    ("Pacific Heights", "Embarcadero"): 10,
    ("Pacific Heights", "Haight-Ashbury"): 11,
    ("Pacific Heights", "Fisherman's Wharf"): 13,
    ("Pacific Heights", "Mission District"): 15,
    ("Pacific Heights", "Alamo Square"): 10,
    ("Pacific Heights", "Bayview"): 22,
    ("Pacific Heights", "Richmond District"): 12,
    ("North Beach", "Golden Gate Park"): 22,
    ("North Beach", "Embarcadero"): 6,
    ("North Beach", "Haight-Ashbury"): 18,
    ("North Beach", "Fisherman's Wharf"): 5,
    ("North Beach", "Mission District"): 18,
    ("North Beach", "Alamo Square"): 16,
    ("North Beach", "Bayview"): 25,
    ("North Beach", "Richmond District"): 18,
    ("Golden Gate Park", "Embarcadero"): 25,
    ("Golden Gate Park", "Haight-Ashbury"): 7,
    ("Golden Gate Park", "Fisherman's Wharf"): 24,
    ("Golden Gate Park", "Mission District"): 17,
    ("Golden Gate Park", "Alamo Square"): 9,
    ("Golden Gate Park", "Bayview"): 23,
    ("Golden Gate Park", "Richmond District"): 7,
    ("Embarcadero", "Haight-Ashbury"): 20,
    ("Embarcadero", "Fisherman's Wharf"): 6,
    ("Embarcadero", "Mission District"): 20,
    ("Embarcadero", "Alamo Square"): 19,
    ("Embarcadero", "Bayview"): 21,
    ("Embarcadero", "Richmond District"): 21,
    ("Haight-Ashbury", "Golden Gate Park"): 7,
    ("Haight-Ashbury", "Fisherman's Wharf"): 23,
    ("Haight-Ashbury", "Mission District"): 11,
    ("Haight-Ashbury", "Alamo Square"): 5,
    ("Haight-Ashbury", "Bayview"): 18,
    ("Haight-Ashbury", "Richmond District"): 10,
    ("Fisherman's Wharf", "Golden Gate Park"): 25,
    ("Fisherman's Wharf", "Mission District"): 22,
    ("Fisherman's Wharf", "Alamo Square"): 21,
    ("Fisherman's Wharf", "Bayview"): 26,
    ("Fisherman's Wharf", "Richmond District"): 18,
    ("Mission District", "Golden Gate Park"): 17,
    ("Mission District", "Haight-Ashbury"): 12,
    ("Mission District", "Alamo Square"): 10,
    ("Mission District", "Bayview"): 14,
    ("Mission District", "Richmond District"): 20,
    ("Alamo Square", "Golden Gate Park"): 9,
    ("Alamo Square", "Bayview"): 16,
    ("Alamo Square", "Richmond District"): 11,
    ("Bayview", "Richmond District"): 25,
}

# Define meeting constraints
meetings = [
    {"name": "Emily", "location": "Pacific Heights", "start": "9:15", "end": "13:45", "min_time": 120},
    {"name": "Helen", "location": "North Beach", "start": "13:45", "end": "18:45", "min_time": 30},
    {"name": "Kimberly", "location": "Golden Gate Park", "start": "18:45", "end": "21:15", "min_time": 75},
    {"name": "James", "location": "Embarcadero", "start": "10:30", "end": "11:30", "min_time": 30},
    {"name": "Linda", "location": "Haight-Ashbury", "start": "7:30", "end": "19:15", "min_time": 15},
    {"name": "Paul", "location": "Fisherman's Wharf", "start": "14:45", "end": "18:45", "min_time": 90},
    {"name": "Anthony", "location": "Mission District", "start": "8:00", "end": "14:45", "min_time": 105},
    {"name": "Nancy", "location": "Alamo Square", "start": "8:30", "end": "13:45", "min_time": 120},
    {"name": "William", "location": "Bayview", "start": "17:30", "end": "20:30", "min_time": 120},
    {"name": "Margaret", "location": "Richmond District", "start": "15:15", "end": "18:15", "min_time": 45},
]

start_time = datetime.strptime("9:00", "%H:%M")
itinerary = []

# Helper function to compute available meeting slots
def find_meeting(start, end, location, duration):
    duration = timedelta(minutes=duration)
    available_slots = []
    
    for meeting in meetings:
        if meeting["location"] == location:
            meeting_start = datetime.strptime(meeting["start"], "%H:%M")
            meeting_end = datetime.strptime(meeting["end"], "%H:%M")
            meeting_start = meeting_start.replace(year=start.year, month=start.month, day=start.day)
            meeting_end = meeting_end.replace(year=start.year, month=start.month, day=start.day)
            
            if meeting_start >= start and meeting_end <= end:
                available_slots.append((meeting_start, meeting_end, meeting["name"], meeting["min_time"]))
    
    return available_slots

# Initial schedule calculation
def schedule_meetings():
    current_time = start_time
    # Check for each person based on availability
    for meeting in meetings:
        location = meeting["location"]
        available_times = find_meeting(current_time, current_time + timedelta(hours=3), location, meeting["min_time"])
        
        for start, end, person_name, min_time in available_times:
            if (end - start) >= timedelta(minutes=min_time):
                end_time = start + timedelta(minutes=min_time)
                travel_time = travel_times.get((current_time.strftime("%H:%M"), location), 0)
                current_time += timedelta(minutes=travel_time)
                itinerary.append({
                    "action": "meet",
                    "location": location,
                    "person": person_name,
                    "start_time": end_time.strftime("%H:%M"),
                    "end_time": (end_time + timedelta(minutes=min_time)).strftime("%H:%M")
                })
                current_time = end_time + timedelta(minutes=travel_time)

schedule_meetings()

# Generate final itinerary
result = {
    "itinerary": itinerary
}

# Output result in JSON format
print(json.dumps(result, indent=2))