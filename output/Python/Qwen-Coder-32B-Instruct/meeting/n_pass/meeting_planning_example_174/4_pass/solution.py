import json
from datetime import datetime, timedelta

def time_to_minutes(time_str):
    h, m = map(int, time_str.split(':'))
    return h * 60 + m

def minutes_to_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02}"

def calculate_schedule():
    start_time = time_to_minutes("9:00")
    locations = {
        "Nob Hill": 0,
        "Pacific Heights": 8,
        "Mission District": 13
    }
    travel_times = {
        ("Nob Hill", "Pacific Heights"): 8,
        ("Nob Hill", "Mission District"): 13,
        ("Pacific Heights", "Nob Hill"): 8,
        ("Pacific Heights", "Mission District"): 15,
        ("Mission District", "Nob Hill"): 12,
        ("Mission District", "Pacific Heights"): 16
    }
    meetings = {
        "Thomas": {"location": "Pacific Heights", "start": time_to_minutes("15:30"), "end": time_to_minutes("19:15"), "min_duration": 75},
        "Kenneth": {"location": "Mission District", "start": time_to_minutes("12:00"), "end": time_to_minutes("15:45"), "min_duration": 45}
    }
    
    itinerary = []
    current_location = "Nob Hill"
    current_time = start_time
    
    def can_meet(person, start_time):
        meeting = meetings[person]
        return meeting["start"] <= start_time <= meeting["end"] - meeting["min_duration"]
    
    def add_meeting(person, start_time):
        meeting = meetings[person]
        end_time = min(start_time + meeting["min_duration"], meeting["end"])
        itinerary.append({
            "action": "meet",
            "location": meeting["location"],
            "person": person,
            "start_time": minutes_to_time(start_time),
            "end_time": minutes_to_time(end_time)
        })
        return end_time
    
    # Try to meet each person if possible
    for person in meetings:
        meeting = meetings[person]
        travel_time = travel_times[(current_location, meeting["location"])]
        potential_start_time = current_time + travel_time
        
        if can_meet(person, potential_start_time):
            current_time = potential_start_time
            current_location = meeting["location"]
            current_time = add_meeting(person, current_time)
        else:
            # If we can't meet at the earliest possible time, try other times within the meeting window
            for t in range(meeting["start"], meeting["end"] - meeting["min_duration"] + 1):
                potential_start_time = t - travel_time
                if current_time <= potential_start_time and can_meet(person, t):
                    current_time = potential_start_time
                    current_location = meeting["location"]
                    current_time = add_meeting(person, t)
                    break
    
    return itinerary

schedule = calculate_schedule()
print(json.dumps({"itinerary": schedule}))