import json
from datetime import datetime, timedelta

# Function to calculate the end time after adding duration (in minutes) to a given start time
def add_minutes(start_time, minutes):
    return start_time + timedelta(minutes=minutes)

# Class to represent a meeting
class Meeting:
    def __init__(self, person, location, start_time, duration):
        self.person = person
        self.location = location
        self.start_time = start_time
        self.end_time = add_minutes(self.start_time, duration)

    def to_dict(self):
        return {
            "action": "meet",
            "location": self.location,
            "person": self.person,
            "start_time": self.start_time.strftime("%H:%M"),
            "end_time": self.end_time.strftime("%H:%M"),
        }

# Travel distances in minutes
travel_times = {
    ("Nob Hill", "Presidio"): 17,
    ("Nob Hill", "North Beach"): 8,
    ("Nob Hill", "Fisherman's Wharf"): 11,
    ("Nob Hill", "Pacific Heights"): 8,
    ("Presidio", "Nob Hill"): 18,
    ("Presidio", "North Beach"): 18,
    ("Presidio", "Fisherman's Wharf"): 19,
    ("Presidio", "Pacific Heights"): 11,
    ("North Beach", "Nob Hill"): 7,
    ("North Beach", "Presidio"): 17,
    ("North Beach", "Fisherman's Wharf"): 5,
    ("North Beach", "Pacific Heights"): 8,
    ("Fisherman's Wharf", "Nob Hill"): 11,
    ("Fisherman's Wharf", "Presidio"): 17,
    ("Fisherman's Wharf", "North Beach"): 6,
    ("Fisherman's Wharf", "Pacific Heights"): 12,
    ("Pacific Heights", "Nob Hill"): 8,
    ("Pacific Heights", "Presidio"): 11,
    ("Pacific Heights", "North Beach"): 9,
    ("Pacific Heights", "Fisherman's Wharf"): 13,
}

# Meeting constraints
meetings = {
    "Jeffrey": {"location": "Presidio", "available": (datetime.strptime("08:00", "%H:%M"),
                                                      datetime.strptime("10:00", "%H:%M")), 
                "duration": 105},
    "Steven": {"location": "North Beach", "available": (datetime.strptime("13:30", "%H:%M"),
                                                       datetime.strptime("22:00", "%H:%M")), 
               "duration": 45},
    "Barbara": {"location": "Fisherman's Wharf", "available": (datetime.strptime("18:00", "%H:%M"),
                                                             datetime.strptime("21:30", "%H:%M")), 
                "duration": 30},
    "John": {"location": "Pacific Heights", "available": (datetime.strptime("09:00", "%H:%M"),
                                                          datetime.strptime("13:30", "%H:%M")), 
             "duration": 15},
}

# Start time
current_time = datetime.strptime("09:00", "%H:%M")
itinerary = []

# Meeting sequence
def schedule_meetings(current_time):
    for person, info in meetings.items():
        start = info["available"][0]
        end = info["available"][1]
        duration = info["duration"]
        
        # Check if we can meet this person
        if current_time < start:
            current_time = start  # Wait until they are available
            
        # Calculate travel time to meeting location
        travel_time = travel_times.get(("Nob Hill", info["location"]), 0)
        start_meeting_time = add_minutes(current_time, travel_time)
        
        # Check if we can fit the meeting in the available window
        if start_meeting_time + timedelta(minutes=duration) <= end:
            meeting = Meeting(person, info["location"], start_meeting_time, duration)
            itinerary.append(meeting.to_dict())
            # Update current time to the end of the meeting + travel back
            current_time = add_minutes(meeting.end_time, travel_times.get((info["location"], "Nob Hill"), 0))

# Call the scheduling function
schedule_meetings(current_time)

# Convert output to JSON
result = {"itinerary": itinerary}
print(json.dumps(result, indent=2))