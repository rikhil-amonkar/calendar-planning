import json
from datetime import datetime, timedelta

# Travel distances in minutes
travel_times = {
    ("Bayview", "North Beach"): 21,
    ("Bayview", "Presidio"): 31,
    ("Bayview", "Haight-Ashbury"): 19,
    ("Bayview", "Union Square"): 17,
    ("North Beach", "Bayview"): 22,
    ("North Beach", "Presidio"): 17,
    ("North Beach", "Haight-Ashbury"): 18,
    ("North Beach", "Union Square"): 7,
    ("Presidio", "Bayview"): 31,
    ("Presidio", "North Beach"): 18,
    ("Presidio", "Haight-Ashbury"): 15,
    ("Presidio", "Union Square"): 22,
    ("Haight-Ashbury", "Bayview"): 18,
    ("Haight-Ashbury", "North Beach"): 19,
    ("Haight-Ashbury", "Presidio"): 15,
    ("Haight-Ashbury", "Union Square"): 17,
    ("Union Square", "Bayview"): 15,
    ("Union Square", "North Beach"): 10,
    ("Union Square", "Presidio"): 24,
    ("Union Square", "Haight-Ashbury"): 18,
}

# Meeting constraints
meetings = {
    "Barbara": {"location": "North Beach", "start": "13:45", "end": "20:15", "duration": 60},
    "Margaret": {"location": "Presidio", "start": "10:15", "end": "15:15", "duration": 30},
    "Kevin": {"location": "Haight-Ashbury", "start": "20:00", "end": "20:45", "duration": 30},
    "Kimberly": {"location": "Union Square", "start": "07:45", "end": "16:45", "duration": 30}
}

# Starting point and time
start_location = "Bayview"
arrival_time = datetime.strptime("09:00", "%H:%M")

# Function to attempt to schedule meetings
def schedule_meetings():
    current_time = arrival_time
    itinerary = []

    # Meet Kimberly first since her time window is the earliest
    kim_location = meetings["Kimberly"]["location"]
    kim_start = datetime.strptime(meetings["Kimberly"]["start"], "%H:%M")
    kim_end = datetime.strptime(meetings["Kimberly"]["end"], "%H:%M")

    travel_to_kim = travel_times[(start_location, kim_location)]
    current_time += timedelta(minutes=travel_to_kim)

    if current_time < kim_start:
        current_time = kim_start
    
    meet_kim_start = current_time
    meet_kim_end = meet_kim_start + timedelta(minutes=meetings["Kimberly"]["duration"])

    itinerary.append({
        "action": "meet",
        "location": kim_location,
        "person": "Kimberly",
        "start_time": meet_kim_start.strftime("%H:%M"),
        "end_time": meet_kim_end.strftime("%H:%M"),
    })

    # Travel to Margaret next
    next_location = meetings["Margaret"]["location"]
    travel_to_margaret = travel_times[(kim_location, next_location)]
    current_time += timedelta(minutes=travel_to_margaret)

    margaret_start = datetime.strptime(meetings["Margaret"]["start"], "%H:%M")
    margaret_end = datetime.strptime(meetings["Margaret"]["end"], "%H:%M")

    if current_time < margaret_start:
        current_time = margaret_start
    
    meet_margaret_start = current_time
    meet_margaret_end = meet_margaret_start + timedelta(minutes=meetings["Margaret"]["duration"])

    itinerary.append({
        "action": "meet",
        "location": next_location,
        "person": "Margaret",
        "start_time": meet_margaret_start.strftime("%H:%M"),
        "end_time": meet_margaret_end.strftime("%H:%M"),
    })

    # Travel to Barbara next
    next_location = meetings["Barbara"]["location"]
    travel_to_barbara = travel_times[(next_location, next_location)]
    current_time += timedelta(minutes=travel_to_barbara)

    barbara_start = datetime.strptime(meetings["Barbara"]["start"], "%H:%M")
    barbara_end = datetime.strptime(meetings["Barbara"]["end"], "%H:%M")

    if current_time < barbara_start:
        current_time = barbara_start
    
    meet_barbara_start = current_time
    meet_barbara_end = meet_barbara_start + timedelta(minutes=meetings["Barbara"]["duration"])

    itinerary.append({
        "action": "meet",
        "location": next_location,
        "person": "Barbara",
        "start_time": meet_barbara_start.strftime("%H:%M"),
        "end_time": meet_barbara_end.strftime("%H:%M"),
    })

    # Finally, travel to Kevin
    next_location = meetings["Kevin"]["location"]
    travel_to_kevin = travel_times[(next_location, next_location)]
    current_time += timedelta(minutes=travel_to_kevin)

    kevin_start = datetime.strptime(meetings["Kevin"]["start"], "%H:%M")
    kevin_end = datetime.strptime(meetings["Kevin"]["end"], "%H:%M")

    if current_time < kevin_start:
        current_time = kevin_start

    meet_kevin_start = current_time
    meet_kevin_end = meet_kevin_start + timedelta(minutes=meetings["Kevin"]["duration"])

    itinerary.append({
        "action": "meet",
        "location": next_location,
        "person": "Kevin",
        "start_time": meet_kevin_start.strftime("%H:%M"),
        "end_time": meet_kevin_end.strftime("%H:%M"),
    })

    return {"itinerary": itinerary}

# Execute scheduling and output result as JSON
result = schedule_meetings()
print(json.dumps(result, indent=2))