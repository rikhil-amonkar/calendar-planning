import json
from datetime import datetime, timedelta

# Define travel times
travel_times = {
    ("Marina District", "Mission District"): 20,
    ("Marina District", "Fisherman's Wharf"): 10,
    ("Marina District", "Presidio"): 10,
    ("Marina District", "Union Square"): 16,
    ("Marina District", "Sunset District"): 19,
    ("Marina District", "Financial District"): 17,
    ("Marina District", "Haight-Ashbury"): 16,
    ("Marina District", "Russian Hill"): 8,
    ("Mission District", "Marina District"): 19,
    ("Mission District", "Fisherman's Wharf"): 22,
    ("Mission District", "Presidio"): 25,
    ("Mission District", "Union Square"): 15,
    ("Mission District", "Sunset District"): 24,
    ("Mission District", "Financial District"): 15,
    ("Mission District", "Haight-Ashbury"): 12,
    ("Mission District", "Russian Hill"): 15,
    ("Fisherman's Wharf", "Marina District"): 9,
    ("Fisherman's Wharf", "Mission District"): 22,
    ("Fisherman's Wharf", "Presidio"): 17,
    ("Fisherman's Wharf", "Union Square"): 13,
    ("Fisherman's Wharf", "Sunset District"): 27,
    ("Fisherman's Wharf", "Financial District"): 11,
    ("Fisherman's Wharf", "Haight-Ashbury"): 22,
    ("Fisherman's Wharf", "Russian Hill"): 7,
    ("Presidio", "Marina District"): 11,
    ("Presidio", "Mission District"): 26,
    ("Presidio", "Fisherman's Wharf"): 19,
    ("Presidio", "Union Square"): 22,
    ("Presidio", "Sunset District"): 15,
    ("Presidio", "Financial District"): 23,
    ("Presidio", "Haight-Ashbury"): 15,
    ("Presidio", "Russian Hill"): 14,
    ("Union Square", "Marina District"): 18,
    ("Union Square", "Mission District"): 14,
    ("Union Square", "Fisherman's Wharf"): 15,
    ("Union Square", "Presidio"): 24,
    ("Union Square", "Sunset District"): 27,
    ("Union Square", "Financial District"): 9,
    ("Union Square", "Haight-Ashbury"): 18,
    ("Union Square", "Russian Hill"): 13,
    ("Sunset District", "Marina District"): 21,
    ("Sunset District", "Mission District"): 25,
    ("Sunset District", "Fisherman's Wharf"): 29,
    ("Sunset District", "Presidio"): 16,
    ("Sunset District", "Union Square"): 30,
    ("Sunset District", "Financial District"): 30,
    ("Sunset District", "Haight-Ashbury"): 15,
    ("Sunset District", "Russian Hill"): 24,
    ("Financial District", "Marina District"): 15,
    ("Financial District", "Mission District"): 17,
    ("Financial District", "Fisherman's Wharf"): 10,
    ("Financial District", "Presidio"): 22,
    ("Financial District", "Union Square"): 9,
    ("Financial District", "Sunset District"): 30,
    ("Financial District", "Haight-Ashbury"): 19,
    ("Financial District", "Russian Hill"): 11,
    ("Haight-Ashbury", "Marina District"): 17,
    ("Haight-Ashbury", "Mission District"): 11,
    ("Haight-Ashbury", "Fisherman's Wharf"): 23,
    ("Haight-Ashbury", "Presidio"): 15,
    ("Haight-Ashbury", "Union Square"): 19,
    ("Haight-Ashbury", "Sunset District"): 15,
    ("Haight-Ashbury", "Financial District"): 21,
    ("Haight-Ashbury", "Russian Hill"): 17,
    ("Russian Hill", "Marina District"): 7,
    ("Russian Hill", "Mission District"): 16,
    ("Russian Hill", "Fisherman's Wharf"): 7,
    ("Russian Hill", "Presidio"): 14,
    ("Russian Hill", "Union Square"): 10,
    ("Russian Hill", "Sunset District"): 23,
    ("Russian Hill", "Financial District"): 11,
    ("Russian Hill", "Haight-Ashbury"): 17,
}

# Define meeting constraints
meetings = {
    "Karen": {"location": "Mission District", "start": "14:15", "end": "22:00", "duration": 30},
    "Richard": {"location": "Fisherman's Wharf", "start": "14:30", "end": "17:30", "duration": 30},
    "Robert": {"location": "Presidio", "start": "21:45", "end": "22:45", "duration": 60},
    "Joseph": {"location": "Union Square", "start": "11:45", "end": "14:45", "duration": 120},
    "Helen": {"location": "Sunset District", "start": "14:45", "end": "20:45", "duration": 105},
    "Elizabeth": {"location": "Financial District", "start": "10:00", "end": "12:45", "duration": 75},
    "Kimberly": {"location": "Haight-Ashbury", "start": "14:15", "end": "17:30", "duration": 105},
    "Ashley": {"location": "Russian Hill", "start": "11:30", "end": "21:30", "duration": 45},
}

def parse_time(time_str):
    return datetime.strptime(time_str, "%H:%M")

def add_minutes(time, minutes):
    return time + timedelta(minutes=minutes)

def find_next_meeting(current_location, current_time, visited):
    available_meetings = []
    for person, details in meetings.items():
        if person in visited:
            continue
        location = details["location"]
        start_time = parse_time(details["start"])
        end_time = parse_time(details["end"])
        duration = details["duration"]
        
        # Check if we can reach the meeting location in time
        travel_time = travel_times.get((current_location, location), float('inf'))
        arrival_time = add_minutes(current_time, travel_time)
        
        # Check if the meeting is available after travel time
        if arrival_time >= start_time:
            meeting_start = arrival_time
            meeting_end = add_minutes(meeting_start, duration)
            if meeting_end <= end_time:
                available_meetings.append((person, location, meeting_start, meeting_end))
    
    # Sort available meetings by start time
    available_meetings.sort(key=lambda x: x[2])
    return available_meetings

def create_schedule():
    itinerary = []
    current_location = "Marina District"
    current_time = parse_time("9:00")
    visited = set()
    
    while True:
        available_meetings = find_next_meeting(current_location, current_time, visited)
        if not available_meetings:
            break
        
        # Choose the meeting that starts the earliest
        person, location, meeting_start, meeting_end = available_meetings[0]
        itinerary.append({
            "action": "meet",
            "location": location,
            "person": person,
            "start_time": meeting_start.strftime("%H:%M"),
            "end_time": meeting_end.strftime("%H:%M")
        })
        
        visited.add(person)
        current_location = location
        current_time = meeting_end
    
    return itinerary

schedule = create_schedule()
result = {"itinerary": schedule}
print(json.dumps(result, indent=2))