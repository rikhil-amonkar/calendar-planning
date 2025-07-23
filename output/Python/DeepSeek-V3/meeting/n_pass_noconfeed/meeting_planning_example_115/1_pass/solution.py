import json
from datetime import datetime, timedelta

def parse_time(time_str):
    return datetime.strptime(time_str, "%H:%M")

def format_time(dt):
    return dt.strftime("%-H:%M")

def calculate_schedule():
    # Input parameters
    current_location = "Richmond District"
    current_time = parse_time("9:00")
    
    # Friend constraints
    jessica = {
        "location": "Pacific Heights",
        "available_start": parse_time("15:30"),
        "available_end": parse_time("16:45"),
        "min_duration": timedelta(minutes=45)
    }
    
    carol = {
        "location": "Marina District",
        "available_start": parse_time("11:30"),
        "available_end": parse_time("15:00"),
        "min_duration": timedelta(minutes=60)
    }
    
    # Travel times in minutes
    travel_times = {
        ("Richmond District", "Pacific Heights"): 10,
        ("Richmond District", "Marina District"): 9,
        ("Pacific Heights", "Richmond District"): 12,
        ("Pacific Heights", "Marina District"): 6,
        ("Marina District", "Richmond District"): 11,
        ("Marina District", "Pacific Heights"): 7
    }
    
    # Possible schedules (meet Carol first or Jessica first)
    possible_schedules = []
    
    # Option 1: Meet Carol first, then Jessica
    # Travel to Marina District
    travel_time = timedelta(minutes=travel_times[(current_location, carol["location"])])
    arrive_carol = current_time + travel_time
    # Meet Carol
    carol_start = max(arrive_carol, carol["available_start"])
    carol_end = carol_start + carol["min_duration"]
    if carol_end <= carol["available_end"]:
        # Travel to Pacific Heights
        travel_time_jessica = timedelta(minutes=travel_times[(carol["location"], jessica["location"])])
        arrive_jessica = carol_end + travel_time_jessica
        # Meet Jessica
        jessica_start = max(arrive_jessica, jessica["available_start"])
        jessica_end = jessica_start + jessica["min_duration"]
        if jessica_end <= jessica["available_end"]:
            possible_schedules.append([
                {"action": "meet", "location": carol["location"], "person": "Carol", 
                 "start_time": format_time(carol_start), "end_time": format_time(carol_end)},
                {"action": "meet", "location": jessica["location"], "person": "Jessica", 
                 "start_time": format_time(jessica_start), "end_time": format_time(jessica_end)}
            ])
    
    # Option 2: Meet Jessica first, then Carol
    # Travel to Pacific Heights
    travel_time = timedelta(minutes=travel_times[(current_location, jessica["location"])])
    arrive_jessica = current_time + travel_time
    # Check if we can meet Jessica now (but her availability starts at 15:30)
    jessica_start = max(arrive_jessica, jessica["available_start"])
    jessica_end = jessica_start + jessica["min_duration"]
    if jessica_end <= jessica["available_end"]:
        # Travel to Marina District
        travel_time_carol = timedelta(minutes=travel_times[(jessica["location"], carol["location"])])
        arrive_carol = jessica_end + travel_time_carol
        # Meet Carol
        carol_start = max(arrive_carol, carol["available_start"])
        carol_end = carol_start + carol["min_duration"]
        if carol_end <= carol["available_end"]:
            possible_schedules.append([
                {"action": "meet", "location": jessica["location"], "person": "Jessica", 
                 "start_time": format_time(jessica_start), "end_time": format_time(jessica_end)},
                {"action": "meet", "location": carol["location"], "person": "Carol", 
                 "start_time": format_time(carol_start), "end_time": format_time(carol_end)}
            ])
    
    # Select the best schedule (most meetings, or earliest finish)
    if not possible_schedules:
        return {"itinerary": []}
    elif len(possible_schedules) == 1:
        return {"itinerary": possible_schedules[0]}
    else:
        # Prefer the schedule that meets both friends
        return {"itinerary": possible_schedules[0]}

# Calculate and output the schedule
schedule = calculate_schedule()
print(json.dumps(schedule, indent=2))