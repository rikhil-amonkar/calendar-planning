import json
from datetime import datetime, timedelta

def parse_time(time_str):
    return datetime.strptime(time_str, "%H:%M")

def format_time(dt):
    return dt.strftime("%-H:%M")

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
    
    # Possible schedules (Carol first or Jessica first)
    possible_schedules = []
    
    # Option 1: Meet Carol first, then Jessica
    # Go to Marina District to meet Carol
    travel_to_carol = travel_times[(current_location, carol["location"])]
    arrival_carol = add_minutes(current_time, travel_to_carol)
    
    # Determine meeting time with Carol
    carol_start = max(arrival_carol, carol["available_start"])
    carol_end = add_minutes(carol_start, carol["min_duration"])
    if time_diff(carol_start, carol_end) < carol["min_duration"] or parse_time(carol_end) > parse_time(carol["available_end"]):
        pass  # Not possible
    else:
        # Travel to Jessica
        travel_to_jessica = travel_times[(carol["location"], jessica["location"])]
        arrival_jessica = add_minutes(carol_end, travel_to_jessica)
        
        # Determine meeting time with Jessica
        jessica_start = max(arrival_jessica, jessica["available_start"])
        jessica_end = add_minutes(jessica_start, jessica["min_duration"])
        if time_diff(jessica_start, jessica_end) >= jessica["min_duration"] and parse_time(jessica_end) <= parse_time(jessica["available_end"]):
            possible_schedules.append([
                {"action": "meet", "location": carol["location"], "person": "Carol", "start_time": carol_start, "end_time": carol_end},
                {"action": "meet", "location": jessica["location"], "person": "Jessica", "start_time": jessica_start, "end_time": jessica_end}
            ])
    
    # Option 2: Meet Jessica first, then Carol
    # Check if meeting Jessica first is possible (must finish before Carol's availability ends)
    # Travel to Jessica
    travel_to_jessica = travel_times[(current_location, jessica["location"])]
    arrival_jessica = add_minutes(current_time, travel_to_jessica)
    
    # Jessica is only available in the afternoon, so this is impossible (arrival would be 9:10, but Jessica is available at 15:30)
    # So skip this option
    
    # Option 3: Meet only Carol
    carol_start = max(arrival_carol, carol["available_start"])
    carol_end = add_minutes(carol_start, carol["min_duration"])
    if time_diff(carol_start, carol_end) >= carol["min_duration"] and parse_time(carol_end) <= parse_time(carol["available_end"]):
        possible_schedules.append([
            {"action": "meet", "location": carol["location"], "person": "Carol", "start_time": carol_start, "end_time": carol_end}
        ])
    
    # Option 4: Meet only Jessica
    # Travel to Jessica
    travel_to_jessica = travel_times[(current_location, jessica["location"])]
    arrival_jessica = add_minutes(current_time, travel_to_jessica)
    
    jessica_start = max(arrival_jessica, jessica["available_start"])
    jessica_end = add_minutes(jessica_start, jessica["min_duration"])
    if time_diff(jessica_start, jessica_end) >= jessica["min_duration"] and parse_time(jessica_end) <= parse_time(jessica["available_end"]):
        possible_schedules.append([
            {"action": "meet", "location": jessica["location"], "person": "Jessica", "start_time": jessica_start, "end_time": jessica_end}
        ])
    
    # Select the best schedule (most meetings, then earliest finish time)
    best_schedule = []
    for schedule in possible_schedules:
        if len(schedule) > len(best_schedule):
            best_schedule = schedule
        elif len(schedule) == len(best_schedule) and schedule:
            last_meeting_end = parse_time(schedule[-1]["end_time"])
            best_last_end = parse_time(best_schedule[-1]["end_time"]) if best_schedule else last_meeting_end + timedelta(days=1)
            if last_meeting_end < best_last_end:
                best_schedule = schedule
    
    return {"itinerary": best_schedule}

if __name__ == "__main__":
    result = optimize_schedule()
    print(json.dumps(result, indent=2))