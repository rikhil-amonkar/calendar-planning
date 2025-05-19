import json
from datetime import datetime, timedelta

# Define travel distances in minutes
travel_times = {
    ("Presidio", "Richmond District"): 7,
    ("Presidio", "North Beach"): 18,
    ("Presidio", "Financial District"): 23,
    ("Presidio", "Golden Gate Park"): 12,
    ("Presidio", "Union Square"): 22,
    ("Richmond District", "North Beach"): 17,
    ("Richmond District", "Financial District"): 22,
    ("Richmond District", "Golden Gate Park"): 9,
    ("Richmond District", "Union Square"): 21,
    ("North Beach", "Financial District"): 7,
    ("North Beach", "Golden Gate Park"): 22,
    ("North Beach", "Union Square"): 7,
    ("Financial District", "Golden Gate Park"): 23,
    ("Financial District", "Union Square"): 9,
    ("Golden Gate Park", "Union Square"): 22,
}

def add_minutes(start_time, minutes):
    return start_time + timedelta(minutes=minutes)

# Meeting constraints
meetings = {
    "Jason": {"location": "Richmond District", "available_from": "13:00", "available_to": "20:45", "min_duration": 90},
    "Melissa": {"location": "North Beach", "available_from": "18:45", "available_to": "20:15", "min_duration": 45},
    "Brian": {"location": "Financial District", "available_from": "09:45", "available_to": "21:45", "min_duration": 15},
    "Elizabeth": {"location": "Golden Gate Park", "available_from": "08:45", "available_to": "21:30", "min_duration": 105},
    "Laura": {"location": "Union Square", "available_from": "14:15", "available_to": "19:30", "min_duration": 75},
}

def generate_itinerary():
    itinerary = []
    current_time = datetime.strptime("09:00", "%H:%M")
    
    # Meet Brian first since he is available right after our arrival
    brian_start = add_minutes(current_time, travel_times[("Presidio", "Financial District")])
    if brian_start < datetime.strptime(meetings["Brian"]["available_from"], "%H:%M"):
        brian_start = datetime.strptime(meetings["Brian"]["available_from"], "%H:%M")
    
    brian_end = add_minutes(brian_start, meetings["Brian"]["min_duration"])
    if brian_end > datetime.strptime(meetings["Brian"]["available_to"], "%H:%M"):
        raise Exception("Unable to meet Brian in available time")
    
    itinerary.append({
        "action": "meet",
        "location": meetings["Brian"]["location"],
        "person": "Brian",
        "start_time": brian_start.strftime("%H:%M"),
        "end_time": brian_end.strftime("%H:%M"),
    })
    
    # Meet Elizabeth next
    current_time = brian_end
    elizabeth_start = add_minutes(current_time, travel_times[("Financial District", "Golden Gate Park")])
    
    if elizabeth_start < datetime.strptime(meetings["Elizabeth"]["available_from"], "%H:%M"):
        elizabeth_start = datetime.strptime(meetings["Elizabeth"]["available_from"], "%H:%M")
    
    elizabeth_end = add_minutes(elizabeth_start, meetings["Elizabeth"]["min_duration"])
    if elizabeth_end > datetime.strptime(meetings["Elizabeth"]["available_to"], "%H:%M"):
        raise Exception("Unable to meet Elizabeth in available time")
    
    itinerary.append({
        "action": "meet",
        "location": meetings["Elizabeth"]["location"],
        "person": "Elizabeth",
        "start_time": elizabeth_start.strftime("%H:%M"),
        "end_time": elizabeth_end.strftime("%H:%M"),
    })
    
    # Meet Jason next
    current_time = elizabeth_end
    jason_start = add_minutes(current_time, travel_times[("Golden Gate Park", "Richmond District")])
    
    if jason_start < datetime.strptime(meetings["Jason"]["available_from"], "%H:%M"):
        jason_start = datetime.strptime(meetings["Jason"]["available_from"], "%H:%M")
    
    jason_end = add_minutes(jason_start, meetings["Jason"]["min_duration"])
    if jason_end > datetime.strptime(meetings["Jason"]["available_to"], "%H:%M"):
        raise Exception("Unable to meet Jason in available time")
    
    itinerary.append({
        "action": "meet",
        "location": meetings["Jason"]["location"],
        "person": "Jason",
        "start_time": jason_start.strftime("%H:%M"),
        "end_time": jason_end.strftime("%H:%M"),
    })
    
    # Meet Laura next
    current_time = jason_end
    laura_start = add_minutes(current_time, travel_times[("Richmond District", "Union Square")])
    
    if laura_start < datetime.strptime(meetings["Laura"]["available_from"], "%H:%M"):
        laura_start = datetime.strptime(meetings["Laura"]["available_from"], "%H:%M")
    
    laura_end = add_minutes(laura_start, meetings["Laura"]["min_duration"])
    if laura_end > datetime.strptime(meetings["Laura"]["available_to"], "%H:%M"):
        raise Exception("Unable to meet Laura in available time")
    
    itinerary.append({
        "action": "meet",
        "location": meetings["Laura"]["location"],
        "person": "Laura",
        "start_time": laura_start.strftime("%H:%M"),
        "end_time": laura_end.strftime("%H:%M"),
    })
    
    # Meet Melissa last
    current_time = laura_end
    melissa_start = add_minutes(current_time, travel_times[("Union Square", "North Beach")])
    
    if melissa_start < datetime.strptime(meetings["Melissa"]["available_from"], "%H:%M"):
        melissa_start = datetime.strptime(meetings["Melissa"]["available_from"], "%H:%M")
    
    melissa_end = add_minutes(melissa_start, meetings["Melissa"]["min_duration"])
    if melissa_end > datetime.strptime(meetings["Melissa"]["available_to"], "%H:%M"):
        raise Exception("Unable to meet Melissa in available time")
    
    itinerary.append({
        "action": "meet",
        "location": meetings["Melissa"]["location"],
        "person": "Melissa",
        "start_time": melissa_start.strftime("%H:%M"),
        "end_time": melissa_end.strftime("%H:%M"),
    })
    
    return {"itinerary": itinerary}

if __name__ == "__main__":
    schedule = generate_itinerary()
    print(json.dumps(schedule, indent=2))