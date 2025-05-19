import json
from datetime import datetime, timedelta

def parse_time(time_str):
    return datetime.strptime(time_str, "%H:%M")

def format_time(dt):
    return dt.strftime("%-H:%M")

def compute_optimal_schedule():
    # Input parameters
    travel_times = {
        ("Financial District", "Chinatown"): 5,
        ("Financial District", "Golden Gate Park"): 23,
        ("Chinatown", "Financial District"): 5,
        ("Chinatown", "Golden Gate Park"): 23,
        ("Golden Gate Park", "Financial District"): 26,
        ("Golden Gate Park", "Chinatown"): 23
    }
    
    current_location = "Financial District"
    current_time = parse_time("9:00")
    
    kenneth_available_start = parse_time("12:00")
    kenneth_available_end = parse_time("15:00")
    kenneth_min_duration = timedelta(minutes=90)
    
    barbara_available_start = parse_time("8:15")
    barbara_available_end = parse_time("19:00")
    barbara_min_duration = timedelta(minutes=45)
    
    itinerary = []
    
    # Option 1: Meet Kenneth first, then Barbara
    option1 = []
    time = current_time
    location = current_location
    
    # Travel to Chinatown to meet Kenneth
    travel_time = travel_times[(location, "Chinatown")]
    time += timedelta(minutes=travel_time)
    location = "Chinatown"
    
    # Meet Kenneth
    kenneth_start = max(time, kenneth_available_start)
    kenneth_end = min(kenneth_start + kenneth_min_duration, kenneth_available_end)
    if kenneth_end - kenneth_start >= kenneth_min_duration:
        option1.append({
            "action": "meet",
            "location": "Chinatown",
            "person": "Kenneth",
            "start_time": format_time(kenneth_start),
            "end_time": format_time(kenneth_end)
        })
        time = kenneth_end
        
        # Travel to Golden Gate Park to meet Barbara
        travel_time = travel_times[(location, "Golden Gate Park")]
        time += timedelta(minutes=travel_time)
        location = "Golden Gate Park"
        
        # Meet Barbara
        barbara_start = max(time, barbara_available_start)
        barbara_end = min(barbara_start + barbara_min_duration, barbara_available_end)
        if barbara_end - barbara_start >= barbara_min_duration:
            option1.append({
                "action": "meet",
                "location": "Golden Gate Park",
                "person": "Barbara",
                "start_time": format_time(barbara_start),
                "end_time": format_time(barbara_end)
            })
    
    # Option 2: Meet Barbara first, then Kenneth
    option2 = []
    time = current_time
    location = current_location
    
    # Travel to Golden Gate Park to meet Barbara
    travel_time = travel_times[(location, "Golden Gate Park")]
    time += timedelta(minutes=travel_time)
    location = "Golden Gate Park"
    
    # Meet Barbara
    barbara_start = max(time, barbara_available_start)
    barbara_end = min(barbara_start + barbara_min_duration, barbara_available_end)
    if barbara_end - barbara_start >= barbara_min_duration:
        option2.append({
            "action": "meet",
            "location": "Golden Gate Park",
            "person": "Barbara",
            "start_time": format_time(barbara_start),
            "end_time": format_time(barbara_end)
        })
        time = barbara_end
        
        # Travel to Chinatown to meet Kenneth
        travel_time = travel_times[(location, "Chinatown")]
        time += timedelta(minutes=travel_time)
        location = "Chinatown"
        
        # Meet Kenneth
        kenneth_start = max(time, kenneth_available_start)
        kenneth_end = min(kenneth_start + kenneth_min_duration, kenneth_available_end)
        if kenneth_end - kenneth_start >= kenneth_min_duration:
            option2.append({
                "action": "meet",
                "location": "Chinatown",
                "person": "Kenneth",
                "start_time": format_time(kenneth_start),
                "end_time": format_time(kenneth_end)
            })
    
    # Determine the best option
    if len(option1) == 2 and len(option2) == 2:
        # Both options are valid, choose the one that finishes earlier
        option1_end = parse_time(option1[-1]["end_time"])
        option2_end = parse_time(option2[-1]["end_time"])
        itinerary = option1 if option1_end <= option2_end else option2
    elif len(option1) == 2:
        itinerary = option1
    elif len(option2) == 2:
        itinerary = option2
    else:
        # Try to meet at least one person
        if len(option1) > 0 or len(option2) > 0:
            itinerary = option1 if len(option1) > len(option2) else option2
    
    return {"itinerary": itinerary}

result = compute_optimal_schedule()
print(json.dumps(result, indent=2))