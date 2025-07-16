import json
from datetime import datetime, timedelta

def parse_time(time_str):
    return datetime.strptime(time_str, "%H:%M")

def format_time(time_obj):
    return time_obj.strftime("%-H:%M")

def calculate_schedule():
    # Input parameters
    travel_times = {
        ("The Castro", "Mission District"): 7,
        ("The Castro", "Financial District"): 20,
        ("Mission District", "The Castro"): 7,
        ("Mission District", "Financial District"): 17,
        ("Financial District", "The Castro"): 23,
        ("Financial District", "Mission District"): 17
    }
    
    current_location = "The Castro"
    current_time = parse_time("9:00")
    
    laura_available_start = parse_time("12:15")
    laura_available_end = parse_time("19:45")
    laura_min_duration = 75  # minutes
    
    anthony_available_start = parse_time("12:30")
    anthony_available_end = parse_time("14:45")
    anthony_min_duration = 30  # minutes
    
    itinerary = []
    
    # Option 1: Meet Laura first, then Anthony
    option1_itinerary = []
    option1_valid = True
    
    # Travel to Mission District to meet Laura
    travel_time = travel_times[(current_location, "Mission District")]
    arrival_time = current_time + timedelta(minutes=travel_time)
    
    # Determine meeting time with Laura
    laura_start = max(arrival_time, laura_available_start)
    laura_end = laura_start + timedelta(minutes=laura_min_duration)
    
    if laura_end > laura_available_end:
        option1_valid = False
    else:
        option1_itinerary.append({
            "action": "meet",
            "location": "Mission District",
            "person": "Laura",
            "start_time": format_time(laura_start),
            "end_time": format_time(laura_end)
        })
        
        # Travel to Financial District to meet Anthony
        travel_time = travel_times[("Mission District", "Financial District")]
        arrival_time = laura_end + timedelta(minutes=travel_time)
        
        # Determine meeting time with Anthony
        anthony_start = max(arrival_time, anthony_available_start)
        anthony_end = anthony_start + timedelta(minutes=anthony_min_duration)
        
        if anthony_end > anthony_available_end:
            option1_valid = False
        else:
            option1_itinerary.append({
                "action": "meet",
                "location": "Financial District",
                "person": "Anthony",
                "start_time": format_time(anthony_start),
                "end_time": format_time(anthony_end)
            })
    
    # Option 2: Meet Anthony first, then Laura
    option2_itinerary = []
    option2_valid = True
    
    # Travel to Financial District to meet Anthony
    travel_time = travel_times[(current_location, "Financial District")]
    arrival_time = current_time + timedelta(minutes=travel_time)
    
    # Determine meeting time with Anthony
    anthony_start = max(arrival_time, anthony_available_start)
    anthony_end = anthony_start + timedelta(minutes=anthony_min_duration)
    
    if anthony_end > anthony_available_end:
        option2_valid = False
    else:
        option2_itinerary.append({
            "action": "meet",
            "location": "Financial District",
            "person": "Anthony",
            "start_time": format_time(anthony_start),
            "end_time": format_time(anthony_end)
        })
        
        # Travel to Mission District to meet Laura
        travel_time = travel_times[("Financial District", "Mission District")]
        arrival_time = anthony_end + timedelta(minutes=travel_time)
        
        # Determine meeting time with Laura
        laura_start = max(arrival_time, laura_available_start)
        laura_end = laura_start + timedelta(minutes=laura_min_duration)
        
        if laura_end > laura_available_end:
            option2_valid = False
        else:
            option2_itinerary.append({
                "action": "meet",
                "location": "Mission District",
                "person": "Laura",
                "start_time": format_time(laura_start),
                "end_time": format_time(laura_end)
            })
    
    # Determine which option is better
    if option1_valid and option2_valid:
        # Both options are valid, choose the one that meets Laura earlier
        laura_time1 = parse_time(option1_itinerary[0]["start_time"])
        laura_time2 = parse_time(option2_itinerary[1]["start_time"])
        if laura_time1 < laura_time2:
            itinerary = option1_itinerary
        else:
            itinerary = option2_itinerary
    elif option1_valid:
        itinerary = option1_itinerary
    elif option2_valid:
        itinerary = option2_itinerary
    
    return {"itinerary": itinerary}

result = calculate_schedule()
print(json.dumps(result, indent=2))