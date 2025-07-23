import json
from datetime import datetime, timedelta

def parse_time(time_str):
    return datetime.strptime(time_str, "%H:%M")

def format_time(dt):
    return dt.strftime("%-H:%M")

def calculate_schedule():
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
    
    # Try meeting Barbara first
    option1 = []
    temp_location = current_location
    temp_time = current_time
    
    # Travel to Golden Gate Park to meet Barbara
    travel_key = (temp_location, "Golden Gate Park")
    travel_duration = timedelta(minutes=travel_times[travel_key])
    arrival_time = temp_time + travel_duration
    
    # Meet Barbara
    barbara_meet_start = max(arrival_time, barbara_available_start)
    barbara_meet_end = barbara_meet_start + barbara_min_duration
    
    if barbara_meet_end <= barbara_available_end:
        option1.append({
            "action": "travel",
            "location": "Golden Gate Park",
            "start_time": format_time(temp_time),
            "end_time": format_time(arrival_time)
        })
        option1.append({
            "action": "meet",
            "location": "Golden Gate Park",
            "person": "Barbara",
            "start_time": format_time(barbara_meet_start),
            "end_time": format_time(barbara_meet_end)
        })
        
        # Travel to Chinatown to meet Kenneth
        travel_key = ("Golden Gate Park", "Chinatown")
        travel_duration = timedelta(minutes=travel_times[travel_key])
        arrival_time = barbara_meet_end + travel_duration
        
        # Meet Kenneth
        kenneth_meet_start = max(arrival_time, kenneth_available_start)
        kenneth_meet_end = kenneth_meet_start + kenneth_min_duration
        
        if kenneth_meet_start <= kenneth_available_end and kenneth_meet_end <= kenneth_available_end:
            option1.append({
                "action": "travel",
                "location": "Chinatown",
                "start_time": format_time(barbara_meet_end),
                "end_time": format_time(arrival_time)
            })
            option1.append({
                "action": "meet",
                "location": "Chinatown",
                "person": "Kenneth",
                "start_time": format_time(kenneth_meet_start),
                "end_time": format_time(kenneth_meet_end)
            })
    
    # Try meeting Kenneth first
    option2 = []
    temp_location = current_location
    temp_time = current_time
    
    # Travel to Chinatown to meet Kenneth
    travel_key = (temp_location, "Chinatown")
    travel_duration = timedelta(minutes=travel_times[travel_key])
    arrival_time = temp_time + travel_duration
    
    # Meet Kenneth
    kenneth_meet_start = max(arrival_time, kenneth_available_start)
    kenneth_meet_end = kenneth_meet_start + kenneth_min_duration
    
    if kenneth_meet_end <= kenneth_available_end:
        option2.append({
            "action": "travel",
            "location": "Chinatown",
            "start_time": format_time(temp_time),
            "end_time": format_time(arrival_time)
        })
        option2.append({
            "action": "meet",
            "location": "Chinatown",
            "person": "Kenneth",
            "start_time": format_time(kenneth_meet_start),
            "end_time": format_time(kenneth_meet_end)
        })
        
        # Travel to Golden Gate Park to meet Barbara
        travel_key = ("Chinatown", "Golden Gate Park")
        travel_duration = timedelta(minutes=travel_times[travel_key])
        arrival_time = kenneth_meet_end + travel_duration
        
        # Meet Barbara
        barbara_meet_start = max(arrival_time, barbara_available_start)
        barbara_meet_end = barbara_meet_start + barbara_min_duration
        
        if barbara_meet_end <= barbara_available_end:
            option2.append({
                "action": "travel",
                "location": "Golden Gate Park",
                "start_time": format_time(kenneth_meet_end),
                "end_time": format_time(arrival_time)
            })
            option2.append({
                "action": "meet",
                "location": "Golden Gate Park",
                "person": "Barbara",
                "start_time": format_time(barbara_meet_start),
                "end_time": format_time(barbara_meet_end)
            })
    
    # Determine which option is better (more meetings or longer duration)
    if len(option1) == 4 and len(option2) == 4:
        # Both options work, choose the one with earlier finish time
        option1_finish = parse_time(option1[-1]["end_time"])
        option2_finish = parse_time(option2[-1]["end_time"])
        itinerary = option1 if option1_finish < option2_finish else option2
    elif len(option1) == 4:
        itinerary = option1
    elif len(option2) == 4:
        itinerary = option2
    else:
        # Can't meet both, try meeting just one
        # Try meeting Barbara
        temp_location = current_location
        temp_time = current_time
        travel_key = (temp_location, "Golden Gate Park")
        travel_duration = timedelta(minutes=travel_times[travel_key])
        arrival_time = temp_time + travel_duration
        barbara_meet_start = max(arrival_time, barbara_available_start)
        barbara_meet_end = barbara_meet_start + barbara_min_duration
        if barbara_meet_end <= barbara_available_end:
            itinerary = [
                {
                    "action": "travel",
                    "location": "Golden Gate Park",
                    "start_time": format_time(temp_time),
                    "end_time": format_time(arrival_time)
                },
                {
                    "action": "meet",
                    "location": "Golden Gate Park",
                    "person": "Barbara",
                    "start_time": format_time(barbara_meet_start),
                    "end_time": format_time(barbara_meet_end)
                }
            ]
        else:
            # Try meeting Kenneth
            temp_location = current_location
            temp_time = current_time
            travel_key = (temp_location, "Chinatown")
            travel_duration = timedelta(minutes=travel_times[travel_key])
            arrival_time = temp_time + travel_duration
            kenneth_meet_start = max(arrival_time, kenneth_available_start)
            kenneth_meet_end = kenneth_meet_start + kenneth_min_duration
            if kenneth_meet_end <= kenneth_available_end:
                itinerary = [
                    {
                        "action": "travel",
                        "location": "Chinatown",
                        "start_time": format_time(temp_time),
                        "end_time": format_time(arrival_time)
                    },
                    {
                        "action": "meet",
                        "location": "Chinatown",
                        "person": "Kenneth",
                        "start_time": format_time(kenneth_meet_start),
                        "end_time": format_time(kenneth_meet_end)
                    }
                ]
    
    # Prepare the output
    output = {
        "itinerary": itinerary
    }
    
    return json.dumps(output, indent=2)

print(calculate_schedule())