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

def compute_schedule():
    # Input parameters
    travel_times = {
        ("Sunset District", "Chinatown"): 30,
        ("Sunset District", "Russian Hill"): 24,
        ("Sunset District", "North Beach"): 29,
        ("Chinatown", "Sunset District"): 29,
        ("Chinatown", "Russian Hill"): 7,
        ("Chinatown", "North Beach"): 3,
        ("Russian Hill", "Sunset District"): 23,
        ("Russian Hill", "Chinatown"): 9,
        ("Russian Hill", "North Beach"): 5,
        ("North Beach", "Sunset District"): 27,
        ("North Beach", "Chinatown"): 6,
        ("North Beach", "Russian Hill"): 4,
    }

    current_location = "Sunset District"
    current_time = "9:00"
    itinerary = []

    # Melissa at North Beach 8:15-13:30, min 105 minutes
    melissa_start = "8:15"
    melissa_end = "13:30"
    travel_time = travel_times[(current_location, "North Beach")]
    arrival_time = add_minutes(current_time, travel_time)
    
    if arrival_time < melissa_start:
        start_meeting = melissa_start
    else:
        start_meeting = arrival_time
    
    end_meeting = add_minutes(start_meeting, 105)
    
    if end_meeting > melissa_end:
        possible_duration = time_diff(start_meeting, melissa_end)
        if possible_duration >= 60:  # Fallback to minimum 60 minutes if 105 not possible
            end_meeting = melissa_end
        else:
            # Skip Melissa if can't meet minimum
            pass
    else:
        itinerary.append({
            "action": "meet",
            "location": "North Beach",
            "person": "Melissa",
            "start_time": start_meeting,
            "end_time": end_meeting
        })
        current_location = "North Beach"
        current_time = end_meeting

    # Anthony at Chinatown 13:15-14:30, min 60 minutes
    anthony_start = "13:15"
    anthony_end = "14:30"
    travel_time = travel_times[(current_location, "Chinatown")]
    arrival_time = add_minutes(current_time, travel_time)
    
    if arrival_time < anthony_start:
        start_meeting = anthony_start
    else:
        start_meeting = arrival_time
    
    end_meeting = add_minutes(start_meeting, 60)
    
    if end_meeting > anthony_end:
        possible_duration = time_diff(start_meeting, anthony_end)
        if possible_duration >= 30:  # Fallback to minimum 30 minutes if 60 not possible
            end_meeting = anthony_end
        else:
            # Skip Anthony if can't meet minimum
            pass
    else:
        itinerary.append({
            "action": "meet",
            "location": "Chinatown",
            "person": "Anthony",
            "start_time": start_meeting,
            "end_time": end_meeting
        })
        current_location = "Chinatown"
        current_time = end_meeting

    # Rebecca at Russian Hill 19:30-21:15, min 105 minutes
    rebecca_start = "19:30"
    rebecca_end = "21:15"
    travel_time = travel_times[(current_location, "Russian Hill")]
    arrival_time = add_minutes(current_time, travel_time)
    
    if arrival_time < rebecca_start:
        start_meeting = rebecca_start
    else:
        start_meeting = arrival_time
    
    end_meeting = add_minutes(start_meeting, 105)
    
    if end_meeting > rebecca_end:
        possible_duration = time_diff(start_meeting, rebecca_end)
        if possible_duration >= 60:  # Fallback to minimum 60 minutes if 105 not possible
            end_meeting = rebecca_end
        else:
            # Skip Rebecca if can't meet minimum
            pass
    else:
        itinerary.append({
            "action": "meet",
            "location": "Russian Hill",
            "person": "Rebecca",
            "start_time": start_meeting,
            "end_time": end_meeting
        })

    return {"itinerary": itinerary}

if __name__ == "__main__":
    schedule = compute_schedule()
    print(json.dumps(schedule, indent=2))