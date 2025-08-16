import json
from datetime import datetime, timedelta

# Input parameters
travel_times = {
    ("Pacific Heights", "Presidio"): 11,
    ("Pacific Heights", "Marina District"): 6,
    ("Presidio", "Pacific Heights"): 11,
    ("Presidio", "Marina District"): 10,
    ("Marina District", "Pacific Heights"): 7,
    ("Marina District", "Presidio"): 10
}

constraints = {
    "Jason": {"location": "Presidio", "available_from": "10:00", "available_to": "16:15", "min_meeting_time": 90},
    "Kenneth": {"location": "Marina District", "available_from": "15:30", "available_to": "16:45", "min_meeting_time": 45}
}

start_location = "Pacific Heights"
start_time = datetime.strptime("9:00", "%H:%M")

def parse_time(time_str):
    return datetime.strptime(time_str, "%H:%M")

def add_minutes(time, minutes):
    return time + timedelta(minutes=minutes)

def find_meeting_times(constraint, current_time):
    available_from = parse_time(constraint["available_from"])
    available_to = parse_time(constraint["available_to"])
    min_meeting_time = constraint["min_meeting_time"]
    
    if current_time >= available_to:
        return None
    
    if current_time < available_from:
        current_time = available_from
    
    end_time = add_minutes(current_time, min_meeting_time)
    if end_time > available_to:
        return None
    
    return current_time, end_time

def calculate_schedule():
    itinerary = []
    current_time = start_time
    current_location = start_location
    
    # Try to meet Jason first
    jason_constraint = constraints["Jason"]
    jason_meeting_times = find_meeting_times(jason_constraint, current_time)
    
    if jason_meeting_times:
        jason_start, jason_end = jason_meeting_times
        travel_time_to_jason = travel_times[(current_location, jason_constraint["location"])]
        jason_start_with_travel = add_minutes(current_time, travel_time_to_jason)
        
        if jason_start_with_travel <= jason_start:
            itinerary.append({
                "action": "travel",
                "location": jason_constraint["location"],
                "start_time": current_time.strftime("%H:%M"),
                "end_time": jason_start_with_travel.strftime("%H:%M")
            })
            current_time = jason_start_with_travel
            current_location = jason_constraint["location"]
        else:
            return {}  # Cannot meet Jason within his availability
        
        itinerary.append({
            "action": "meet",
            "location": jason_constraint["location"],
            "person": "Jason",
            "start_time": jason_start.strftime("%H:%M"),
            "end_time": jason_end.strftime("%H:%M")
        })
        current_time = jason_end
    
    # Try to meet Kenneth next
    kenneth_constraint = constraints["Kenneth"]
    kenneth_meeting_times = find_meeting_times(kenneth_constraint, current_time)
    
    if kenneth_meeting_times:
        kenneth_start, kenneth_end = kenneth_meeting_times
        travel_time_to_kenneth = travel_times[(current_location, kenneth_constraint["location"])]
        kenneth_start_with_travel = add_minutes(current_time, travel_time_to_kenneth)
        
        if kenneth_start_with_travel <= kenneth_start:
            itinerary.append({
                "action": "travel",
                "location": kenneth_constraint["location"],
                "start_time": current_time.strftime("%H:%M"),
                "end_time": kenneth_start_with_travel.strftime("%H:%M")
            })
            current_time = kenneth_start_with_travel
            current_location = kenneth_constraint["location"]
        else:
            return {}  # Cannot meet Kenneth within his availability
        
        itinerary.append({
            "action": "meet",
            "location": kenneth_constraint["location"],
            "person": "Kenneth",
            "start_time": kenneth_start.strftime("%H:%M"),
            "end_time": kenneth_end.strftime("%H:%M")
        })
    
    return {"itinerary": itinerary}

schedule = calculate_schedule()
print(json.dumps(schedule))