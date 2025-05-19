import json
from datetime import datetime, timedelta

# Define travel times in minutes
travel_times = {
    ("Golden Gate Park", "Alamo Square"): 10,
    ("Golden Gate Park", "Presidio"): 11,
    ("Golden Gate Park", "Russian Hill"): 19,
    ("Alamo Square", "Golden Gate Park"): 9,
    ("Alamo Square", "Presidio"): 18,
    ("Alamo Square", "Russian Hill"): 13,
    ("Presidio", "Golden Gate Park"): 12,
    ("Presidio", "Alamo Square"): 18,
    ("Presidio", "Russian Hill"): 14,
    ("Russian Hill", "Golden Gate Park"): 21,
    ("Russian Hill", "Alamo Square"): 15,
    ("Russian Hill", "Presidio"): 14,
}

# Meeting constraints
meetings = {
    "Timothy": {
        "location": "Alamo Square",
        "available_from": datetime.strptime("12:00", "%H:%M"),
        "available_to": datetime.strptime("16:15", "%H:%M"),
        "min_duration": timedelta(minutes=105)
    },
    "Mark": {
        "location": "Presidio",
        "available_from": datetime.strptime("18:45", "%H:%M"),
        "available_to": datetime.strptime("21:00", "%H:%M"),
        "min_duration": timedelta(minutes=60)
    },
    "Joseph": {
        "location": "Russian Hill",
        "available_from": datetime.strptime("16:45", "%H:%M"),
        "available_to": datetime.strptime("21:30", "%H:%M"),
        "min_duration": timedelta(minutes=60)
    }
}

# Start time at Golden Gate Park
start_time = datetime.strptime("09:00", "%H:%M")
itinerary = []

# Function to calculate the optimal schedule
def calculate_schedule(start_time, travel_times, meetings):
    current_time = start_time

    # Meeting with Timothy
    if current_time < meetings["Timothy"]["available_from"]:
        current_time = meetings["Timothy"]["available_from"]
    
    travel_to_timothy = travel_times[("Golden Gate Park", "Alamo Square")]
    
    if current_time + timedelta(minutes=travel_to_timothy) < meetings["Timothy"]["available_to"]:
        meet_start_time = current_time + timedelta(minutes=travel_to_timothy)
        meet_end_time = meet_start_time + meetings["Timothy"]["min_duration"]
        if meet_end_time <= meetings["Timothy"]["available_to"]:
            itinerary.append({
                "action": "meet",
                "location": "Alamo Square",
                "person": "Timothy",
                "start_time": meet_start_time.strftime("%H:%M"),
                "end_time": meet_end_time.strftime("%H:%M"),
            })
            
            # Update current time after meeting Timothy
            current_time = meet_end_time
    
    # Travel to Presidio to meet Mark
    travel_to_mark = travel_times[("Alamo Square", "Presidio")]
    if current_time + timedelta(minutes=travel_to_mark) < meetings["Mark"]["available_to"]:
        current_time += timedelta(minutes=travel_to_mark)
        meet_start_time = current_time
        meet_end_time = meet_start_time + meetings["Mark"]["min_duration"]
        
        if meet_end_time <= meetings["Mark"]["available_to"]:
            itinerary.append({
                "action": "meet",
                "location": "Presidio",
                "person": "Mark",
                "start_time": meet_start_time.strftime("%H:%M"),
                "end_time": meet_end_time.strftime("%H:%M"),
            })
            
            # Update current time after meeting Mark
            current_time = meet_end_time

    # Travel to Russian Hill to meet Joseph
    travel_to_joseph = travel_times[("Presidio", "Russian Hill")]
    if current_time + timedelta(minutes=travel_to_joseph) < meetings["Joseph"]["available_to"]:
        current_time += timedelta(minutes=travel_to_joseph)
        meet_start_time = current_time
        meet_end_time = meet_start_time + meetings["Joseph"]["min_duration"]
        
        if meet_end_time <= meetings["Joseph"]["available_to"]:
            itinerary.append({
                "action": "meet",
                "location": "Russian Hill",
                "person": "Joseph",
                "start_time": meet_start_time.strftime("%H:%M"),
                "end_time": meet_end_time.strftime("%H:%M"),
            })

# Calculate the schedule
calculate_schedule(start_time, travel_times, meetings)

# Output the result as JSON
output = {
    "itinerary": itinerary
}

print(json.dumps(output, indent=2))