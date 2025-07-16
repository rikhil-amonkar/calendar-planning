import json
from datetime import datetime, timedelta

def parse_time(time_str):
    return datetime.strptime(time_str, "%H:%M")

def format_time(dt):
    return dt.strftime("%-H:%M")

def calculate_schedule():
    # Input parameters
    arrival_time = parse_time("9:00")
    karen_available_start = parse_time("18:45")
    karen_available_end = parse_time("20:15")
    karen_min_duration = timedelta(minutes=90)
    mark_available_start = parse_time("13:00")
    mark_available_end = parse_time("17:45")
    mark_min_duration = timedelta(minutes=120)
    
    # Travel times in minutes
    travel_times = {
        ("North Beach", "Pacific Heights"): 8,
        ("North Beach", "Embarcadero"): 6,
        ("Pacific Heights", "North Beach"): 9,
        ("Pacific Heights", "Embarcadero"): 10,
        ("Embarcadero", "North Beach"): 5,
        ("Embarcadero", "Pacific Heights"): 11
    }
    
    current_location = "North Beach"
    current_time = arrival_time
    itinerary = []
    
    # Try to meet Mark first
    mark_travel_time = travel_times[(current_location, "Embarcadero")]
    mark_arrival_time = current_time + timedelta(minutes=mark_travel_time)
    
    if mark_arrival_time <= mark_available_end - mark_min_duration:
        mark_start_time = max(mark_arrival_time, mark_available_start)
        mark_end_time = mark_start_time + mark_min_duration
        
        if mark_end_time <= mark_available_end:
            itinerary.append({
                "action": "meet",
                "location": "Embarcadero",
                "person": "Mark",
                "start_time": format_time(mark_start_time),
                "end_time": format_time(mark_end_time)
            })
            
            # Travel to Karen after meeting Mark
            current_time = mark_end_time
            current_location = "Embarcadero"
            karen_travel_time = travel_times[(current_location, "Pacific Heights")]
            karen_arrival_time = current_time + timedelta(minutes=karen_travel_time)
            
            if karen_arrival_time <= karen_available_end - karen_min_duration:
                karen_start_time = max(karen_arrival_time, karen_available_start)
                karen_end_time = karen_start_time + karen_min_duration
                
                if karen_end_time <= karen_available_end:
                    itinerary.append({
                        "action": "meet",
                        "location": "Pacific Heights",
                        "person": "Karen",
                        "start_time": format_time(karen_start_time),
                        "end_time": format_time(karen_end_time)
                    })
                    return {"itinerary": itinerary}
    
    # If meeting Mark first doesn't work, try meeting Karen first
    current_location = "North Beach"
    current_time = arrival_time
    itinerary = []
    
    karen_travel_time = travel_times[(current_location, "Pacific Heights")]
    karen_arrival_time = current_time + timedelta(minutes=karen_travel_time)
    
    if karen_arrival_time <= karen_available_end - karen_min_duration:
        karen_start_time = max(karen_arrival_time, karen_available_start)
        karen_end_time = karen_start_time + karen_min_duration
        
        if karen_end_time <= karen_available_end:
            itinerary.append({
                "action": "meet",
                "location": "Pacific Heights",
                "person": "Karen",
                "start_time": format_time(karen_start_time),
                "end_time": format_time(karen_end_time)
            })
            
            # Travel to Mark after meeting Karen
            current_time = karen_end_time
            current_location = "Pacific Heights"
            mark_travel_time = travel_times[(current_location, "Embarcadero")]
            mark_arrival_time = current_time + timedelta(minutes=mark_travel_time)
            
            if mark_arrival_time <= mark_available_end - mark_min_duration:
                mark_start_time = max(mark_arrival_time, mark_available_start)
                mark_end_time = mark_start_time + mark_min_duration
                
                if mark_end_time <= mark_available_end:
                    itinerary.append({
                        "action": "meet",
                        "location": "Embarcadero",
                        "person": "Mark",
                        "start_time": format_time(mark_start_time),
                        "end_time": format_time(mark_end_time)
                    })
                    return {"itinerary": itinerary}
    
    # If neither works, try meeting only one person
    # Try meeting Mark only
    current_location = "North Beach"
    current_time = arrival_time
    itinerary = []
    
    mark_travel_time = travel_times[(current_location, "Embarcadero")]
    mark_arrival_time = current_time + timedelta(minutes=mark_travel_time)
    
    if mark_arrival_time <= mark_available_end - mark_min_duration:
        mark_start_time = max(mark_arrival_time, mark_available_start)
        mark_end_time = mark_start_time + mark_min_duration
        
        if mark_end_time <= mark_available_end:
            itinerary.append({
                "action": "meet",
                "location": "Embarcadero",
                "person": "Mark",
                "start_time": format_time(mark_start_time),
                "end_time": format_time(mark_end_time)
            })
            return {"itinerary": itinerary}
    
    # Try meeting Karen only
    current_location = "North Beach"
    current_time = arrival_time
    itinerary = []
    
    karen_travel_time = travel_times[(current_location, "Pacific Heights")]
    karen_arrival_time = current_time + timedelta(minutes=karen_travel_time)
    
    if karen_arrival_time <= karen_available_end - karen_min_duration:
        karen_start_time = max(karen_arrival_time, karen_available_start)
        karen_end_time = karen_start_time + karen_min_duration
        
        if karen_end_time <= karen_available_end:
            itinerary.append({
                "action": "meet",
                "location": "Pacific Heights",
                "person": "Karen",
                "start_time": format_time(karen_start_time),
                "end_time": format_time(karen_end_time)
            })
            return {"itinerary": itinerary}
    
    # If nothing works, return empty itinerary
    return {"itinerary": []}

result = calculate_schedule()
print(json.dumps(result, indent=2))