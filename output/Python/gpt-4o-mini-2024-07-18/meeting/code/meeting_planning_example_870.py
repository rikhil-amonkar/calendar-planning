import json
from datetime import datetime, timedelta
import itertools

# Define the travel distances in minutes
travel_times = {
    ("Pacific Heights", "Marina District"): 6,
    ("Pacific Heights", "The Castro"): 16,
    ("Pacific Heights", "Richmond District"): 12,
    ("Pacific Heights", "Alamo Square"): 10,
    ("Pacific Heights", "Financial District"): 13,
    ("Pacific Heights", "Presidio"): 11,
    ("Pacific Heights", "Mission District"): 15,
    ("Pacific Heights", "Nob Hill"): 8,
    ("Pacific Heights", "Russian Hill"): 7,
    ("Marina District", "Pacific Heights"): 7,
    ("Marina District", "The Castro"): 22,
    ("Marina District", "Richmond District"): 11,
    ("Marina District", "Alamo Square"): 15,
    ("Marina District", "Financial District"): 17,
    ("Marina District", "Presidio"): 10,
    ("Marina District", "Mission District"): 20,
    ("Marina District", "Nob Hill"): 12,
    ("Marina District", "Russian Hill"): 8,
    ("The Castro", "Pacific Heights"): 16,
    ("The Castro", "Marina District"): 21,
    ("The Castro", "Richmond District"): 16,
    ("The Castro", "Alamo Square"): 8,
    ("The Castro", "Financial District"): 21,
    ("The Castro", "Presidio"): 20,
    ("The Castro", "Mission District"): 7,
    ("The Castro", "Nob Hill"): 16,
    ("The Castro", "Russian Hill"): 18,
    ("Richmond District", "Pacific Heights"): 10,
    ("Richmond District", "Marina District"): 9,
    ("Richmond District", "The Castro"): 16,
    ("Richmond District", "Alamo Square"): 13,
    ("Richmond District", "Financial District"): 22,
    ("Richmond District", "Presidio"): 7,
    ("Richmond District", "Mission District"): 20,
    ("Richmond District", "Nob Hill"): 17,
    ("Richmond District", "Russian Hill"): 13,
    ("Alamo Square", "Pacific Heights"): 10,
    ("Alamo Square", "Marina District"): 15,
    ("Alamo Square", "The Castro"): 8,
    ("Alamo Square", "Richmond District"): 11,
    ("Alamo Square", "Financial District"): 17,
    ("Alamo Square", "Presidio"): 17,
    ("Alamo Square", "Mission District"): 10,
    ("Alamo Square", "Nob Hill"): 11,
    ("Alamo Square", "Russian Hill"): 13,
    ("Financial District", "Pacific Heights"): 13,
    ("Financial District", "Marina District"): 15,
    ("Financial District", "The Castro"): 20,
    ("Financial District", "Richmond District"): 21,
    ("Financial District", "Alamo Square"): 17,
    ("Financial District", "Presidio"): 22,
    ("Financial District", "Mission District"): 17,
    ("Financial District", "Nob Hill"): 8,
    ("Financial District", "Russian Hill"): 11,
    ("Presidio", "Pacific Heights"): 11,
    ("Presidio", "Marina District"): 11,
    ("Presidio", "The Castro"): 21,
    ("Presidio", "Richmond District"): 7,
    ("Presidio", "Alamo Square"): 19,
    ("Presidio", "Financial District"): 23,
    ("Presidio", "Mission District"): 26,
    ("Presidio", "Nob Hill"): 18,
    ("Presidio", "Russian Hill"): 14,
    ("Mission District", "Pacific Heights"): 16,
    ("Mission District", "Marina District"): 19,
    ("Mission District", "The Castro"): 7,
    ("Mission District", "Richmond District"): 20,
    ("Mission District", "Alamo Square"): 11,
    ("Mission District", "Financial District"): 15,
    ("Mission District", "Presidio"): 25,
    ("Mission District", "Nob Hill"): 12,
    ("Mission District", "Russian Hill"): 15,
    ("Nob Hill", "Pacific Heights"): 8,
    ("Nob Hill", "Marina District"): 11,
    ("Nob Hill", "The Castro"): 17,
    ("Nob Hill", "Richmond District"): 14,
    ("Nob Hill", "Alamo Square"): 11,
    ("Nob Hill", "Financial District"): 9,
    ("Nob Hill", "Presidio"): 17,
    ("Nob Hill", "Mission District"): 13,
    ("Nob Hill", "Russian Hill"): 5,
    ("Russian Hill", "Pacific Heights"): 7,
    ("Russian Hill", "Marina District"): 7,
    ("Russian Hill", "The Castro"): 21,
    ("Russian Hill", "Richmond District"): 14,
    ("Russian Hill", "Alamo Square"): 15,
    ("Russian Hill", "Financial District"): 11,
    ("Russian Hill", "Presidio"): 14,
    ("Russian Hill", "Mission District"): 16,
    ("Russian Hill", "Nob Hill"): 5,
}

# Define the friends' constraints
friends = [
    {"name": "Linda", "location": "Marina District", "start": "18:00", "end": "22:00", "duration": 30},
    {"name": "Kenneth", "location": "The Castro", "start": "14:45", "end": "16:15", "duration": 30},
    {"name": "Kimberly", "location": "Richmond District", "start": "14:15", "end": "22:00", "duration": 30},
    {"name": "Paul", "location": "Alamo Square", "start": "21:00", "end": "21:30", "duration": 15},
    {"name": "Carol", "location": "Financial District", "start": "10:15", "end": "12:00", "duration": 60},
    {"name": "Brian", "location": "Presidio", "start": "10:00", "end": "21:30", "duration": 75},
    {"name": "Laura", "location": "Mission District", "start": "16:15", "end": "20:30", "duration": 30},
    {"name": "Sandra", "location": "Nob Hill", "start": "09:15", "end": "18:30", "duration": 60},
    {"name": "Karen", "location": "Russian Hill", "start": "18:30", "end": "22:00", "duration": 75},
]

# Convert time strings to datetime objects
for friend in friends:
    friend["start"] = datetime.strptime(friend["start"], "%H:%M")
    friend["end"] = datetime.strptime(friend["end"], "%H:%M")
    friend["duration"] = timedelta(minutes=friend["duration"])

# Determine best meeting schedule
def find_schedule(friends):
    itinerary = []
    current_time = datetime.strptime("09:00", "%H:%M")
    current_location = "Pacific Heights"

    # List of possible locations
    locations = [friend["location"] for friend in friends]

    while friends:
        for friend in friends:
            travel_time = travel_times.get((current_location, friend["location"]), float('inf'))
            meet_start_time = current_time + timedelta(minutes=travel_time)

            if meet_start_time < friend["start"]:
                current_time = friend["start"] - timedelta(minutes=travel_time)
                meet_start_time = current_time + timedelta(minutes=travel_time)
                
            meet_end_time = meet_start_time + friend["duration"]

            # Check if time is within friend's availability
            if friend["start"] <= meet_start_time < friend["end"] and meet_end_time <= friend["end"]:
                itinerary.append({
                    "action": "meet",
                    "location": friend["location"],
                    "person": friend["name"],
                    "start_time": meet_start_time.strftime("%H:%M"),
                    "end_time": meet_end_time.strftime("%H:%M")
                })
                current_time = meet_end_time + timedelta(minutes=travel_time)  # Move time forward after meeting
                current_location = friend["location"]  # Update current location
                friends.remove(friend)  # Remove from the list after meeting

            # Continue until no more friends left to meet or cannot meet in available time.
            if not friends:
                break

    return itinerary

# Find the optimal meeting schedule
itinerary = find_schedule(friends)

# Output as JSON
result = {"itinerary": itinerary}
print(json.dumps(result, indent=2))