import json
from datetime import datetime, timedelta

# Define the travel distances between locations (in minutes)
travel_times = {
    ("Pacific Heights", "Golden Gate Park"): 15,
    ("Pacific Heights", "The Castro"): 16,
    ("Pacific Heights", "Bayview"): 22,
    ("Pacific Heights", "Marina District"): 6,
    ("Pacific Heights", "Union Square"): 12,
    ("Pacific Heights", "Sunset District"): 21,
    ("Pacific Heights", "Alamo Square"): 10,
    ("Pacific Heights", "Financial District"): 13,
    ("Pacific Heights", "Mission District"): 15,
    ("Golden Gate Park", "The Castro"): 13,
    ("Golden Gate Park", "Bayview"): 23,
    ("Golden Gate Park", "Marina District"): 16,
    ("Golden Gate Park", "Union Square"): 22,
    ("Golden Gate Park", "Sunset District"): 10,
    ("Golden Gate Park", "Alamo Square"): 9,
    ("Golden Gate Park", "Financial District"): 26,
    ("Golden Gate Park", "Mission District"): 17,
    ("The Castro", "Bayview"): 19,
    ("The Castro", "Marina District"): 21,
    ("The Castro", "Union Square"): 19,
    ("The Castro", "Sunset District"): 17,
    ("The Castro", "Alamo Square"): 8,
    ("The Castro", "Financial District"): 21,
    ("The Castro", "Mission District"): 7,
    ("Bayview", "Marina District"): 27,
    ("Bayview", "Union Square"): 18,
    ("Bayview", "Sunset District"): 23,
    ("Bayview", "Alamo Square"): 16,
    ("Bayview", "Financial District"): 19,
    ("Bayview", "Mission District"): 13,
    ("Marina District", "Union Square"): 16,
    ("Marina District", "Sunset District"): 19,
    ("Marina District", "Alamo Square"): 15,
    ("Marina District", "Financial District"): 17,
    ("Marina District", "Mission District"): 20,
    ("Union Square", "Sunset District"): 27,
    ("Union Square", "Alamo Square"): 15,
    ("Union Square", "Financial District"): 9,
    ("Union Square", "Mission District"): 14,
    ("Sunset District", "Alamo Square"): 17,
    ("Sunset District", "Financial District"): 30,
    ("Sunset District", "Mission District"): 25,
    ("Alamo Square", "Financial District"): 17,
}

# Define meeting constraints
meetings = {
    "Helen": {"location": "Golden Gate Park", "start": "09:30", "end": "12:15", "duration": 45},
    "Steven": {"location": "The Castro", "start": "20:15", "end": "22:00", "duration": 105},
    "Deborah": {"location": "Bayview", "start": "08:30", "end": "12:00", "duration": 30},
    "Matthew": {"location": "Marina District", "start": "09:15", "end": "14:15", "duration": 45},
    "Joseph": {"location": "Union Square", "start": "14:15", "end": "18:45", "duration": 120},
    "Ronald": {"location": "Sunset District", "start": "16:00", "end": "20:45", "duration": 60},
    "Robert": {"location": "Alamo Square", "start": "18:30", "end": "21:15", "duration": 120},
    "Rebecca": {"location": "Financial District", "start": "14:45", "end": "16:15", "duration": 30},
    "Elizabeth": {"location": "Mission District", "start": "18:30", "end": "21:00", "duration": 120},
}

# Start planning from Pacific Heights at 9:00AM
start_time = datetime.strptime("09:00", "%H:%M")

# Create a list to hold the meeting schedule
itinerary = []

# Function to check if meeting is possible
def can_meet(start, end, duration):
    available_time = end - start
    return available_time >= timedelta(minutes=duration)

# Function to schedule meetings
def schedule_meetings(initial_time):
    current_time = initial_time
    for friend, details in meetings.items():
        location = details["location"]
        meeting_start = datetime.strptime(details["start"], "%H:%M")
        meeting_end = datetime.strptime(details["end"], "%H:%M")
        duration = details["duration"]
        
        # Adjusted meeting start time considering travel time and previous meetings
        travel_time = travel_times.get(("Pacific Heights", location), float('inf'))
        adjusted_start_time = current_time + timedelta(minutes=travel_time)

        # Check if we can start meeting
        if adjusted_start_time < meeting_start:
            adjusted_start_time = meeting_start
        
        adjusted_end_time = adjusted_start_time + timedelta(minutes=duration)

        if adjusted_end_time <= meeting_end:
            itinerary.append({
                "action": "meet",
                "location": location,
                "person": friend,
                "start_time": adjusted_start_time.strftime("%H:%M"),
                "end_time": adjusted_end_time.strftime("%H:%M")
            })
            # Update the current time to reflect travel time to the next location
            current_time = adjusted_end_time
            # Traveling time to set next location to Pacific Heights after meeting
            current_time += timedelta(minutes=travel_times.get((location, "Pacific Heights"), 0))

# Schedule the meetings
schedule_meetings(start_time)

# Output JSON result
result = {"itinerary": itinerary}
print(json.dumps(result, indent=2))