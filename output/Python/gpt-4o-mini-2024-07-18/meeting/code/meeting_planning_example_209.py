import json
from datetime import datetime, timedelta

# Constants for travel times in minutes
travel_times = {
    "Sunset": {"Chinatown": 30, "Russian Hill": 24, "North Beach": 29},
    "Chinatown": {"Sunset": 29, "Russian Hill": 7, "North Beach": 3},
    "Russian Hill": {"Sunset": 23, "Chinatown": 9, "North Beach": 5},
    "North Beach": {"Sunset": 27, "Chinatown": 6, "Russian Hill": 4},
}

# Meeting availability and constraints
meetings = {
    "Anthony": {"location": "Chinatown", "start": "13:15", "end": "14:30", "duration": 60},
    "Rebecca": {"location": "Russian Hill", "start": "19:30", "end": "21:15", "duration": 105},
    "Melissa": {"location": "North Beach", "start": "08:15", "end": "13:30", "duration": 105},
}

# Start day and time in Sunset District
arrival_time = datetime.strptime("09:00", "%H:%M")

def calculate_schedule():
    itinerary = []

    # Meeting Melissa
    melissa_start = arrival_time + timedelta(minutes=travel_times["Sunset"]["North Beach"])
    if melissa_start.time() < datetime.strptime(meetings["Melissa"]["start"], "%H:%M").time():
        melissa_start = datetime.strptime(meetings["Melissa"]["start"], "%H:%M")
    
    melissa_end = melissa_start + timedelta(minutes=meetings["Melissa"]["duration"])
    
    if melissa_end.time() > datetime.strptime(meetings["Melissa"]["end"], "%H:%M").time():
        melissa_end = datetime.strptime(meetings["Melissa"]["end"], "%H:%M")
    
    itinerary.append({
        "action": "meet",
        "location": meetings["Melissa"]["location"],
        "person": "Melissa",
        "start_time": melissa_start.strftime("%H:%M"),
        "end_time": melissa_end.strftime("%H:%M"),
    })

    # Traveling to Chinatown to meet Anthony
    travel_to_anthony = melissa_end + timedelta(minutes=travel_times["North Beach"]["Chinatown"])
    anthony_start = max(travel_to_anthony, datetime.strptime(meetings["Anthony"]["start"], "%H:%M"))
    anthony_end = anthony_start + timedelta(minutes=meetings["Anthony"]["duration"])

    if anthony_end.time() > datetime.strptime(meetings["Anthony"]["end"], "%H:%M").time():
        anthony_end = datetime.strptime(meetings["Anthony"]["end"], "%H:%M")
    
    itinerary.append({
        "action": "meet",
        "location": meetings["Anthony"]["location"],
        "person": "Anthony",
        "start_time": anthony_start.strftime("%H:%M"),
        "end_time": anthony_end.strftime("%H:%M"),
    })

    # Traveling to Russian Hill to meet Rebecca
    travel_to_rebecca = anthony_end + timedelta(minutes=travel_times["Chinatown"]["Russian Hill"])
    rebecca_start = max(travel_to_rebecca, datetime.strptime(meetings["Rebecca"]["start"], "%H:%M"))
    rebecca_end = rebecca_start + timedelta(minutes=meetings["Rebecca"]["duration"])

    if rebecca_end.time() > datetime.strptime(meetings["Rebecca"]["end"], "%H:%M").time():
        rebecca_end = datetime.strptime(meetings["Rebecca"]["end"], "%H:%M")
    
    itinerary.append({
        "action": "meet",
        "location": meetings["Rebecca"]["location"],
        "person": "Rebecca",
        "start_time": rebecca_start.strftime("%H:%M"),
        "end_time": rebecca_end.strftime("%H:%M"),
    })

    return {"itinerary": itinerary}

# Calculate and output the optimal schedule
optimal_schedule = calculate_schedule()
print(json.dumps(optimal_schedule, indent=2))