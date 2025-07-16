import json
from datetime import datetime, timedelta

def parse_time(time_str):
    return datetime.strptime(time_str, "%H:%M")

def format_time(dt):
    return dt.strftime("%H:%M")

def add_minutes(time_str, minutes):
    dt = parse_time(time_str)
    dt += timedelta(minutes=minutes)
    return format_time(dt)

def time_diff(start_str, end_str):
    start = parse_time(start_str)
    end = parse_time(end_str)
    return (end - start).total_seconds() / 60

def optimize_schedule():
    # Input parameters
    current_location = "Richmond District"
    current_time = "9:00"
    
    # Friend constraints
    jessica = {
        "location": "Pacific Heights",
        "available_start": "15:30",
        "available_end": "16:45",
        "min_duration": 45
    }
    
    carol = {
        "location": "Marina District",
        "available_start": "11:30",
        "available_end": "15:00",
        "min_duration": 60
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
    
    possible_schedules = []
    
    # Option 1: Meet Carol first, then Jessica
    travel_to_carol = travel_times[(current_location, carol["location"])]
    arrival_carol = add_minutes(current_time, travel_to_carol)
    
    # Determine meeting time with Carol
    carol_start = max(arrival_carol, carol["available_start"])
    carol_end = add_minutes(carol_start, carol["min_duration"])
    
    if (parse_time(carol_start) <= parse_time(carol["available_end"]) and \
       (parse_time(carol_end) <= parse_time(carol["available_end"]):
        
        # Travel to Jessica
        travel_to_jessica = travel_times[(carol["location"], jessica["location"])]
        arrival_jessica = add_minutes(carol_end, travel_to_jessica)
        
        # Determine meeting time with Jessica
        jessica_start = max(arrival_jessica, jessica["available_start"])
        jessica_end = add_minutes(jessica_start, jessica["min_duration"])
        
        if (parse_time(jessica_start) <= parse_time(jessica["available_end"]) and \
            parse_time(jessica_end) <= parse_time(jessica["available_end"])):
            possible_schedules.append([
                {"action": "meet", "location": carol["location"], "person": "Carol", 
                 "start_time": carol_start, "end_time": carol_end},
                {"action": "meet", "location": jessica["location"], "person": "Jessica", 
                 "start_time": jessica_start, "end_time": jessica_end}
            ])
    
    # Option 2: Meet only Carol
    travel_to_carol = travel_times[(current_location, carol["location"])]
    arrival_carol = add_minutes(current_time, travel_to_carol)
    
    carol_start = max(arrival_carol, carol["available_start"])
    carol_end = add_minutes(carol_start, carol["min_duration"])
    
    if (parse_time(carol_start) <= parse_time(carol["available_end"]) and \
       (parse_time(carol_end) <= parse_time(carol["available_end"])):
        possible_schedules.append([
            {"action": "meet", "location": carol["location"], "person": "Carol", 
             "start_time": carol_start, "end_time": carol_end}
        ])
    
    # Option 3: Meet only Jessica (only possible if we wait until afternoon)
    # Calculate earliest possible arrival at Jessica's
    earliest_jessica_start = jessica["available_start"]
    travel_to_jessica = travel_times[(current_location, jessica["location"])]
    arrival_jessica = add_minutes(earliest_jessica_start, -travel_to_jessica)
    
    # If we can leave current location early enough to arrive at Jessica's by her available time
    if parse_time(current_time) <= parse_time(arrival_jessica):
        jessica_start = jessica["available_start"]
        jessica_end = add_minutes(jessica_start, jessica["min_duration"])
        
        if parse_time(jessica_end) <= parse_time(jessica["available_end"]):
            possible_schedules.append([
                {"action": "meet", "location": jessica["location"], "person": "Jessica", 
                 "start_time": jessica_start, "end_time": jessica_end}
            ])
    
    # Select the best schedule (most meetings, then earliest finish time)
    best_schedule = []
    for schedule in possible_schedules:
        if len(schedule) > len(best_schedule):
            best_schedule = schedule
        elif len(schedule) == len(best_schedule) and schedule:
            current_end = parse_time(schedule[-1]["end_time"])
            best_end = parse_time(best_schedule[-1]["end_time"]) if best_schedule else current_end + timedelta(days=1)
            if current_end < best_end:
                best_schedule = schedule
    
    return {"itinerary": best_schedule}

if __name__ == "__main__":
    result = optimize_schedule()
    print(json.dumps(result, indent=2))