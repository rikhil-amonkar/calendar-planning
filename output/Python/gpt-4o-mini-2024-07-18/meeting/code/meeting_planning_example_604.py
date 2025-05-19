import json
from datetime import datetime, timedelta

# Define the travel times in minutes as a dictionary
travel_times = {
    ("Fisherman's Wharf", "The Castro"): 26,
    ("Fisherman's Wharf", "Golden Gate Park"): 25,
    ("Fisherman's Wharf", "Embarcadero"): 8,
    ("Fisherman's Wharf", "Russian Hill"): 7,
    ("Fisherman's Wharf", "Nob Hill"): 11,
    ("Fisherman's Wharf", "Alamo Square"): 20,
    ("Fisherman's Wharf", "North Beach"): 6,
    ("The Castro", "Golden Gate Park"): 13,
    ("The Castro", "Embarcadero"): 22,
    ("The Castro", "Russian Hill"): 18,
    ("The Castro", "Nob Hill"): 16,
    ("The Castro", "Alamo Square"): 8,
    ("The Castro", "North Beach"): 20,
    ("Golden Gate Park", "Embarcadero"): 25,
    ("Golden Gate Park", "Russian Hill"): 19,
    ("Golden Gate Park", "Nob Hill"): 20,
    ("Golden Gate Park", "Alamo Square"): 10,
    ("Golden Gate Park", "North Beach"): 24,
    ("Embarcadero", "Russian Hill"): 8,
    ("Embarcadero", "Nob Hill"): 10,
    ("Embarcadero", "Alamo Square"): 19,
    ("Embarcadero", "North Beach"): 5,
    ("Russian Hill", "Nob Hill"): 5,
    ("Russian Hill", "Alamo Square"): 15,
    ("Russian Hill", "North Beach"): 5,
    ("Nob Hill", "Alamo Square"): 11,
    ("Nob Hill", "North Beach"): 8,
    ("Alamo Square", "North Beach"): 15,
}

# Define the meeting constraints
meetings = {
    "Laura": {
        "location": "The Castro",
        "available": ("19:45", "21:30"),
        "duration": 105,
    },
    "Daniel": {
        "location": "Golden Gate Park",
        "available": ("21:15", "21:45"),
        "duration": 15,
    },
    "William": {
        "location": "Embarcadero",
        "available": ("07:00", "09:00"),
        "duration": 90,
    },
    "Karen": {
        "location": "Russian Hill",
        "available": ("14:30", "19:45"),
        "duration": 30,
    },
    "Stephanie": {
        "location": "Nob Hill",
        "available": ("07:30", "09:30"),
        "duration": 45,
    },
    "Joseph": {
        "location": "Alamo Square",
        "available": ("11:30", "12:45"),
        "duration": 15,
    },
    "Kimberly": {
        "location": "North Beach",
        "available": ("15:45", "19:15"),
        "duration": 30,
    },
}

# Start from Fisherman's Wharf at 9:00 AM
start_time = datetime.strptime("09:00", "%H:%M")
itinerary = []
current_time = start_time

# Function to meet a person if the time constraints allow
def can_meet(person, start_time, current_time):
    end_time_limit = datetime.strptime(meetings[person]["available"][1], "%H:%M")
    available_start = datetime.strptime(meetings[person]["available"][0], "%H:%M")
    duration = meetings[person]["duration"]
    
    travel_duration = travel_times.get(("Fisherman's Wharf", meetings[person]["location"]), 0)
    
    if current_time + timedelta(minutes=travel_duration) >= available_start:
        meeting_end_time = current_time + timedelta(minutes=travel_duration) + timedelta(minutes=duration)
        if meeting_end_time <= end_time_limit:
            return meeting_end_time
    return None

# Attempt to schedule meetings in a reasonable order based on availability and preference
def schedule_meetings():
    global current_time
    
    # Meet William first since he is available before 9:00
    if current_time <= datetime.strptime("09:00", "%H:%M"):
        meeting_time = can_meet("William", current_time, current_time)
        if meeting_time:
            itinerary.append({
                "action": "meet",
                "location": meetings["William"]["location"],
                "person": "William",
                "start_time": current_time.strftime("%H:%M"),
                "end_time": meeting_time.strftime("%H:%M"),
            })
            current_time = meeting_time
    
    # Meet Stephanie next
    meeting_time = can_meet("Stephanie", current_time, current_time)
    if meeting_time:
        itinerary.append({
            "action": "meet",
            "location": meetings["Stephanie"]["location"],
            "person": "Stephanie",
            "start_time": current_time.strftime("%H:%M"),
            "end_time": meeting_time.strftime("%H:%M"),
        })
        current_time = meeting_time

    # Meet Joseph afterward
    if current_time < datetime.strptime("11:30", "%H:%M"):
        current_time = datetime.strptime("11:30", "%H:%M")  # Wait until 11:30
    meeting_time = can_meet("Joseph", current_time, current_time)
    if meeting_time:
        itinerary.append({
            "action": "meet",
            "location": meetings["Joseph"]["location"],
            "person": "Joseph",
            "start_time": current_time.strftime("%H:%M"),
            "end_time": meeting_time.strftime("%H:%M"),
        })
        current_time = meeting_time

    # Meet Karen next
    if current_time < datetime.strptime("14:30", "%H:%M"):
        current_time = datetime.strptime("14:30", "%H:%M")  # Wait until 14:30
    meeting_time = can_meet("Karen", current_time, current_time)
    if meeting_time:
        itinerary.append({
            "action": "meet",
            "location": meetings["Karen"]["location"],
            "person": "Karen",
            "start_time": current_time.strftime("%H:%M"),
            "end_time": meeting_time.strftime("%H:%M"),
        })
        current_time = meeting_time

    # Meet Kimberly next
    meeting_time = can_meet("Kimberly", current_time, current_time)
    if meeting_time:
        itinerary.append({
            "action": "meet",
            "location": meetings["Kimberly"]["location"],
            "person": "Kimberly",
            "start_time": current_time.strftime("%H:%M"),
            "end_time": meeting_time.strftime("%H:%M"),
        })
        current_time = meeting_time

    # Finally, meet Laura at The Castro
    if current_time < datetime.strptime("19:45", "%H:%M"):
        current_time = datetime.strptime("19:45", "%H:%M")  # Wait until Laura is available
    meeting_time = can_meet("Laura", current_time, current_time)
    if meeting_time:
        itinerary.append({
            "action": "meet",
            "location": meetings["Laura"]["location"],
            "person": "Laura",
            "start_time": current_time.strftime("%H:%M"),
            "end_time": meeting_time.strftime("%H:%M"),
        })
        current_time = meeting_time

    # Meet Daniel last if time allows
    if current_time < datetime.strptime("21:15", "%H:%M"):
        current_time = datetime.strptime("21:15", "%H:%M")  # Wait until Daniel is available
    meeting_time = can_meet("Daniel", current_time, current_time)
    if meeting_time:
        itinerary.append({
            "action": "meet",
            "location": meetings["Daniel"]["location"],
            "person": "Daniel",
            "start_time": current_time.strftime("%H:%M"),
            "end_time": meeting_time.strftime("%H:%M"),
        })

schedule_meetings()

# Output the final itinerary in JSON format
output = {"itinerary": itinerary}
print(json.dumps(output, indent=2))