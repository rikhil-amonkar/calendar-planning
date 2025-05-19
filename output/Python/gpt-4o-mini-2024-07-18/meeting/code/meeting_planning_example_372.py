import json
from datetime import datetime, timedelta
from itertools import permutations

# Define travel distances in minutes
travel_times = {
    ("Sunset District", "Alamo Square"): 17,
    ("Sunset District", "Russian Hill"): 24,
    ("Sunset District", "Golden Gate Park"): 11,
    ("Sunset District", "Mission District"): 24,
    ("Alamo Square", "Sunset District"): 16,
    ("Alamo Square", "Russian Hill"): 13,
    ("Alamo Square", "Golden Gate Park"): 9,
    ("Alamo Square", "Mission District"): 10,
    ("Russian Hill", "Sunset District"): 23,
    ("Russian Hill", "Alamo Square"): 15,
    ("Russian Hill", "Golden Gate Park"): 21,
    ("Russian Hill", "Mission District"): 16,
    ("Golden Gate Park", "Sunset District"): 10,
    ("Golden Gate Park", "Alamo Square"): 10,
    ("Golden Gate Park", "Russian Hill"): 19,
    ("Golden Gate Park", "Mission District"): 17,
    ("Mission District", "Sunset District"): 24,
    ("Mission District", "Alamo Square"): 11,
    ("Mission District", "Russian Hill"): 15,
    ("Mission District", "Golden Gate Park"): 17,
}

# Define participant availability and required time
participants = {
    "Charles": {"location": "Alamo Square", "available": (datetime.strptime("18:00", "%H:%M"), datetime.strptime("20:45", "%H:%M")), "min_time": 90},
    "Margaret": {"location": "Russian Hill", "available": (datetime.strptime("9:00", "%H:%M"), datetime.strptime("16:00", "%H:%M")), "min_time": 30},
    "Daniel": {"location": "Golden Gate Park", "available": (datetime.strptime("8:00", "%H:%M"), datetime.strptime("13:30", "%H:%M")), "min_time": 15},
    "Stephanie": {"location": "Mission District", "available": (datetime.strptime("20:30", "%H:%M"), datetime.strptime("22:00", "%H:%M")), "min_time": 90},
}

# Define the initial time at Sunset District
start_time = datetime.strptime("9:00", "%H:%M")
itinerary = []

# Create a function to schedule meetings
def schedule_meetings():
    global itinerary
    current_time = start_time
    locations_to_visit = list(participants.keys())
    
    # Order participants for scheduling based on ending time of their availability
    locations_to_visit.sort(key=lambda x: participants[x]["available"][1])
    
    # Loop through each schedule option and check constraints
    for perm in permutations(locations_to_visit):
        temp_time = current_time
        temp_itinerary = []
        is_valid_schedule = True
        
        for person in perm:
            loc = participants[person]["location"]
            visit_start, visit_end = participants[person]["available"]
            min_duration = timedelta(minutes=participants[person]["min_time"])
            
            # Travel time to the location
            if temp_time < visit_start:
                temp_time = visit_start
            
            travel_time = travel_times.get((current_time.strftime("%H:%M"), loc)) or travel_times.get((loc, current_time.strftime("%H:%M")))
            if travel_time:
                temp_time += timedelta(minutes=travel_time)
            
            # Calculate end time for meeting
            meeting_end_time = temp_time + min_duration
            
            # Check if the meeting can fit in the participant's available time
            if meeting_end_time <= visit_end:
                temp_itinerary.append({
                    "action": "meet",
                    "location": loc,
                    "person": person,
                    "start_time": temp_time.strftime("%H:%M"),
                    "end_time": meeting_end_time.strftime("%H:%M"),
                })
                temp_time = meeting_end_time + timedelta(minutes=5)  # Add 5 mins to transition to the next meeting
            else:
                is_valid_schedule = False
                break
        
        if is_valid_schedule and len(temp_itinerary) > len(itinerary):
            itinerary = temp_itinerary

schedule_meetings()

# Convert the result to the required JSON format
result = {
    "itinerary": itinerary
}

# Output the result as JSON
print(json.dumps(result, indent=2))