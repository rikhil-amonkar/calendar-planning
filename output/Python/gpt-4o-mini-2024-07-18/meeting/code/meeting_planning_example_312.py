import json
from datetime import datetime, timedelta

# Travel distances in minutes
travel_times = {
    ("Richmond District", "Sunset District"): 11,
    ("Richmond District", "Haight-Ashbury"): 10,
    ("Richmond District", "Mission District"): 20,
    ("Richmond District", "Golden Gate Park"): 9,
    ("Sunset District", "Richmond District"): 12,
    ("Sunset District", "Haight-Ashbury"): 15,
    ("Sunset District", "Mission District"): 24,
    ("Sunset District", "Golden Gate Park"): 11,
    ("Haight-Ashbury", "Richmond District"): 10,
    ("Haight-Ashbury", "Sunset District"): 15,
    ("Haight-Ashbury", "Mission District"): 11,
    ("Haight-Ashbury", "Golden Gate Park"): 7,
    ("Mission District", "Richmond District"): 20,
    ("Mission District", "Sunset District"): 24,
    ("Mission District", "Haight-Ashbury"): 12,
    ("Mission District", "Golden Gate Park"): 17,
    ("Golden Gate Park", "Richmond District"): 7,
    ("Golden Gate Park", "Sunset District"): 10,
    ("Golden Gate Park", "Haight-Ashbury"): 7,
    ("Golden Gate Park", "Mission District"): 17
}

# Meeting constraints
constraints = {
    "Sarah": {"location": "Sunset District", "start": "10:45", "end": "19:00", "duration": 30},
    "Richard": {"location": "Haight-Ashbury", "start": "11:45", "end": "15:45", "duration": 90},
    "Elizabeth": {"location": "Mission District", "start": "11:00", "end": "17:15", "duration": 120},
    "Michelle": {"location": "Golden Gate Park", "start": "18:15", "end": "20:45", "duration": 90},
}

# Initial time
arrival_time = datetime.strptime("09:00", "%H:%M")

# Function to calculate the optimal meeting schedule
def compute_schedule():
    itinerary = []
    current_time = arrival_time

    # Meeting Sarah first if possible
    if current_time < datetime.strptime(constraints["Sarah"]["start"], "%H:%M"):
        travel_time = travel_times[("Richmond District", "Sunset District")]
        current_time += timedelta(minutes=travel_time)
    
    if current_time < datetime.strptime(constraints["Sarah"]["end"], "%H:%M") - timedelta(minutes=30):
        meet_start = max(current_time, datetime.strptime(constraints["Sarah"]["start"], "%H:%M"))
        meet_end = meet_start + timedelta(minutes=constraints["Sarah"]["duration"])
        itinerary.append({
            "action": "meet",
            "location": constraints["Sarah"]["location"],
            "person": "Sarah",
            "start_time": meet_start.strftime("%H:%M"),
            "end_time": meet_end.strftime("%H:%M")
        })
        current_time = meet_end
        
        # Travel to Richard
        travel_time = travel_times[("Sunset District", "Haight-Ashbury")]
        current_time += timedelta(minutes=travel_time)
    
    # Meeting Richard next if time allows
    if current_time < datetime.strptime(constraints["Richard"]["end"], "%H:%M") - timedelta(minutes=90):
        meet_start = max(current_time, datetime.strptime(constraints["Richard"]["start"], "%H:%M"))
        meet_end = meet_start + timedelta(minutes=constraints["Richard"]["duration"])
        itinerary.append({
            "action": "meet",
            "location": constraints["Richard"]["location"],
            "person": "Richard",
            "start_time": meet_start.strftime("%H:%M"),
            "end_time": meet_end.strftime("%H:%M")
        })
        current_time = meet_end
        
        # Travel to Elizabeth
        travel_time = travel_times[("Haight-Ashbury", "Mission District")]
        current_time += timedelta(minutes=travel_time)
    
    # Meeting Elizabeth next if time allows
    if current_time < datetime.strptime(constraints["Elizabeth"]["end"], "%H:%M") - timedelta(minutes=120):
        meet_start = max(current_time, datetime.strptime(constraints["Elizabeth"]["start"], "%H:%M"))
        meet_end = meet_start + timedelta(minutes=constraints["Elizabeth"]["duration"])
        itinerary.append({
            "action": "meet",
            "location": constraints["Elizabeth"]["location"],
            "person": "Elizabeth",
            "start_time": meet_start.strftime("%H:%M"),
            "end_time": meet_end.strftime("%H:%M")
        })
        current_time = meet_end
        
        # Travel to Michelle
        travel_time = travel_times[("Mission District", "Golden Gate Park")]
        current_time += timedelta(minutes=travel_time)
    
    # Meeting Michelle if time allows
    if current_time < datetime.strptime(constraints["Michelle"]["end"], "%H:%M") - timedelta(minutes=90):
        meet_start = max(current_time, datetime.strptime(constraints["Michelle"]["start"], "%H:%M"))
        meet_end = meet_start + timedelta(minutes=constraints["Michelle"]["duration"])
        itinerary.append({
            "action": "meet",
            "location": constraints["Michelle"]["location"],
            "person": "Michelle",
            "start_time": meet_start.strftime("%H:%M"),
            "end_time": meet_end.strftime("%H:%M")
        })
    
    return {"itinerary": itinerary}

# Compute the schedule and output as JSON
optimal_schedule = compute_schedule()
print(json.dumps(optimal_schedule, indent=2))