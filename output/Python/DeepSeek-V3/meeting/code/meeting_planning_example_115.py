import json
from datetime import datetime, timedelta

def parse_time(time_str):
    return datetime.strptime(time_str, "%H:%M")

def format_time(dt):
    return dt.strftime("%-H:%M")

def compute_schedule():
    # Input parameters
    start_location = "Richmond District"
    start_time = parse_time("9:00")
    
    # Friend constraints
    jessica = {
        "location": "Pacific Heights",
        "available_start": parse_time("15:30"),
        "available_end": parse_time("16:45"),
        "min_duration": 45
    }
    
    carol = {
        "location": "Marina District",
        "available_start": parse_time("11:30"),
        "available_end": parse_time("15:00"),
        "min_duration": 60
    }
    
    # Travel times in minutes between locations
    travel_times = {
        ("Richmond District", "Pacific Heights"): 10,
        ("Richmond District", "Marina District"): 9,
        ("Pacific Heights", "Richmond District"): 12,
        ("Pacific Heights", "Marina District"): 6,
        ("Marina District", "Richmond District"): 11,
        ("Marina District", "Pacific Heights"): 7
    }
    
    # Corrected travel times dictionary key
    travel_times = {
        ("Richmond District", "Pacific Heights"): 10,
        ("Richmond District", "Marina District"): 9,
        ("Pacific Heights", "Richmond District"): 12,
        ("Pacific Heights", "Marina District"): 6,
        ("Marina District", "Richmond District"): 11,
        ("Marina District", "Pacific Heights"): 7
    }
    
    best_schedule = []
    max_meetings = 0
    
    # Try meeting Carol first
    current_location = start_location
    current_time = start_time
    itinerary = []
    
    # Travel to Carol
    travel_key = (current_location, carol["location"])
    travel_duration = timedelta(minutes=travel_times[travel_key])
    arrival_time = current_time + travel_duration
    
    # Meet Carol
    meet_start = max(arrival_time, carol["available_start"])
    meet_end = meet_start + timedelta(minutes=carol["min_duration"])
    
    if meet_end <= carol["available_end"]:
        itinerary.append({
            "action": "meet",
            "location": carol["location"],
            "person": "Carol",
            "start_time": format_time(meet_start),
            "end_time": format_time(meet_end)
        })
        
        # Travel to Jessica
        current_location = carol["location"]
        current_time = meet_end
        travel_key = (current_location, jessica["location"])
        travel_duration = timedelta(minutes=travel_times[travel_key])
        arrival_time = current_time + travel_duration
        
        # Meet Jessica
        meet_start = max(arrival_time, jessica["available_start"])
        meet_end = meet_start + timedelta(minutes=jessica["min_duration"])
        
        if meet_end <= jessica["available_end"]:
            itinerary.append({
                "action": "meet",
                "location": jessica["location"],
                "person": "Jessica",
                "start_time": format_time(meet_start),
                "end_time": format_time(meet_end)
            })
            
            if len(itinerary) > max_meetings:
                best_schedule = itinerary
                max_meetings = len(itinerary)
    
    # Try meeting Jessica first
    current_location = start_location
    current_time = start_time
    itinerary = []
    
    # Travel to Jessica
    travel_key = (current_location, jessica["location"])
    travel_duration = timedelta(minutes=travel_times[travel_key])
    arrival_time = current_time + travel_duration
    
    # Check if we can meet Jessica first (but she's only available in the afternoon)
    if arrival_time < jessica["available_start"]:
        # Wait until Jessica is available
        arrival_time = jessica["available_start"]
    
    meet_start = arrival_time
    meet_end = meet_start + timedelta(minutes=jessica["min_duration"])
    
    if meet_end <= jessica["available_end"]:
        itinerary.append({
            "action": "meet",
            "location": jessica["location"],
            "person": "Jessica",
            "start_time": format_time(meet_start),
            "end_time": format_time(meet_end)
        })
        
        # Travel to Carol
        current_location = jessica["location"]
        current_time = meet_end
        travel_key = (current_location, carol["location"])
        travel_duration = timedelta(minutes=travel_times[travel_key])
        arrival_time = current_time + travel_duration
        
        # Meet Carol
        meet_start = arrival_time
        meet_end = meet_start + timedelta(minutes=carol["min_duration"])
        
        if meet_start >= carol["available_start"] and meet_end <= carol["available_end"]:
            itinerary.append({
                "action": "meet",
                "location": carol["location"],
                "person": "Carol",
                "start_time": format_time(meet_start),
                "end_time": format_time(meet_end)
            })
            
            if len(itinerary) > max_meetings:
                best_schedule = itinerary
                max_meetings = len(itinerary)
        elif meet_start < carol["available_start"]:
            # Can't meet Carol after Jessica because Carol's window ends before we can arrive
            pass
    
    # If both attempts fail, try meeting just one person
    if max_meetings == 0:
        # Try meeting Carol only
        current_location = start_location
        current_time = start_time
        travel_key = (current_location, carol["location"])
        travel_duration = timedelta(minutes=travel_times[travel_key])
        arrival_time = current_time + travel_duration
        
        meet_start = max(arrival_time, carol["available_start"])
        meet_end = meet_start + timedelta(minutes=carol["min_duration"])
        
        if meet_end <= carol["available_end"]:
            best_schedule = [{
                "action": "meet",
                "location": carol["location"],
                "person": "Carol",
                "start_time": format_time(meet_start),
                "end_time": format_time(meet_end)
            }]
            max_meetings = 1
        
        # Try meeting Jessica only
        current_location = start_location
        current_time = start_time
        travel_key = (current_location, jessica["location"])
        travel_duration = timedelta(minutes=travel_times[travel_key])
        arrival_time = current_time + travel_duration
        
        if arrival_time < jessica["available_start"]:
            arrival_time = jessica["available_start"]
        
        meet_start = arrival_time
        meet_end = meet_start + timedelta(minutes=jessica["min_duration"])
        
        if meet_end <= jessica["available_end"]:
            if max_meetings < 1:
                best_schedule = [{
                    "action": "meet",
                    "location": jessica["location"],
                    "person": "Jessica",
                    "start_time": format_time(meet_start),
                    "end_time": format_time(meet_end)
                }]
            elif max_meetings == 1:
                # Prefer meeting Carol if we can only meet one
                pass
    
    return {"itinerary": best_schedule}

if __name__ == "__main__":
    schedule = compute_schedule()
    print(json.dumps(schedule, indent=2))