import json
from datetime import datetime, timedelta

# Travel distances in minutes
travel_times = {
    ("Embarcadero", "Bayview"): 21,
    ("Embarcadero", "Chinatown"): 7,
    ("Embarcadero", "Alamo Square"): 19,
    ("Embarcadero", "Nob Hill"): 10,
    ("Embarcadero", "Presidio"): 20,
    ("Embarcadero", "Union Square"): 10,
    ("Embarcadero", "The Castro"): 25,
    ("Embarcadero", "North Beach"): 5,
    ("Embarcadero", "Fisherman's Wharf"): 6,
    ("Embarcadero", "Marina District"): 12,
    ("Bayview", "Chinatown"): 19,
    ("Bayview", "Alamo Square"): 16,
    ("Bayview", "Nob Hill"): 20,
    ("Bayview", "Presidio"): 32,
    ("Bayview", "Union Square"): 18,
    ("Bayview", "The Castro"): 19,
    ("Bayview", "North Beach"): 22,
    ("Bayview", "Fisherman's Wharf"): 25,
    ("Bayview", "Marina District"): 27,
    ("Chinatown", "Alamo Square"): 17,
    ("Chinatown", "Nob Hill"): 9,
    ("Chinatown", "Presidio"): 19,
    ("Chinatown", "Union Square"): 7,
    ("Chinatown", "The Castro"): 22,
    ("Chinatown", "North Beach"): 3,
    ("Chinatown", "Fisherman's Wharf"): 8,
    ("Chinatown", "Marina District"): 12,
    ("Alamo Square", "Nob Hill"): 11,
    ("Alamo Square", "Presidio"): 17,
    ("Alamo Square", "Union Square"): 14,
    ("Alamo Square", "The Castro"): 8,
    ("Alamo Square", "North Beach"): 15,
    ("Alamo Square", "Fisherman's Wharf"): 19,
    ("Nob Hill", "Presidio"): 17,
    ("Nob Hill", "Union Square"): 7,
    ("Nob Hill", "The Castro"): 17,
    ("Nob Hill", "North Beach"): 8,
    ("Nob Hill", "Fisherman's Wharf"): 10,
    ("Presidio", "Union Square"): 24,
    ("Presidio", "The Castro"): 21,
    ("Presidio", "North Beach"): 18,
    ("Presidio", "Fisherman's Wharf"): 19,
    ("Presidio", "Marina District"): 11,
    ("Union Square", "The Castro"): 17,
    ("Union Square", "North Beach"): 10,
    ("Union Square", "Fisherman's Wharf"): 15,
    ("Union Square", "Marina District"): 18,
    ("The Castro", "North Beach"): 20,
    ("The Castro", "Fisherman's Wharf"): 24,
    ("The Castro", "Marina District"): 21,
    ("North Beach", "Fisherman's Wharf"): 6,
    ("Marina District", "Bayview"): 27,
}

# Meeting constraints
meetings = {
    "Matthew": {"location": "Bayview", "start": "19:15", "end": "22:00", "duration": 120},
    "Karen": {"location": "Chinatown", "start": "19:15", "end": "21:15", "duration": 90},
    "Sarah": {"location": "Alamo Square", "start": "20:00", "end": "21:45", "duration": 105},
    "Jessica": {"location": "Nob Hill", "start": "16:30", "end": "18:45", "duration": 120},
    "Stephanie": {"location": "Presidio", "start": "07:30", "end": "10:15", "duration": 60},
    "Mary": {"location": "Union Square", "start": "16:45", "end": "21:30", "duration": 60},
    "Charles": {"location": "The Castro", "start": "16:30", "end": "22:00", "duration": 105},
    "Nancy": {"location": "North Beach", "start": "14:45", "end": "20:00", "duration": 15},
    "Thomas": {"location": "Fisherman's Wharf", "start": "13:30", "end": "19:00", "duration": 30},
    "Brian": {"location": "Marina District", "start": "12:15", "end": "18:00", "duration": 60},
}

# Times
arrival_time = datetime.strptime("09:00", "%H:%M")
current_time = arrival_time

# Itinerary
itinerary = []

def can_meet(start_time, duration, end_time):
    return start_time + timedelta(minutes=duration) <= end_time

# Meeting order based on time constraints
for person, info in meetings.items():
    location = info["location"]
    start_time = datetime.strptime(info["start"], "%H:%M")
    end_time = datetime.strptime(info["end"], "%H:%M")
    duration = info["duration"]
    
    # Travel time calculations
    travel_key = (current_time.strftime("%H:%M"), location)
    
    if current_time.strftime("%H:%M") in travel_times:
        travel_time = travel_times.get((arrival_time.strftime("%H:%M"), location), 0)
    else:
        travel_time = 0
    
    # Can we meet this person?
    if can_meet(current_time + timedelta(minutes=travel_time), duration, end_time):
        # Calculate the meeting start and end times
        meeting_start = current_time + timedelta(minutes=travel_time)
        meeting_end = meeting_start + timedelta(minutes=duration)
        
        # Add meeting to itinerary
        itinerary.append({
            "action": "meet",
            "location": location,
            "person": person,
            "start_time": meeting_start.strftime("%H:%M"),
            "end_time": meeting_end.strftime("%H:%M"),
        })
        
        # Update current time to the end of this meeting
        current_time = meeting_end

# Output as JSON
output = {"itinerary": itinerary}
print(json.dumps(output, indent=4))