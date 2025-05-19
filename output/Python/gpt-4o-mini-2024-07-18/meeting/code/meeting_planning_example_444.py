import json
from datetime import datetime, timedelta
from itertools import permutations

# Define travel times between locations
travel_times = {
    ("Financial District", "Russian Hill"): 10,
    ("Financial District", "Sunset District"): 31,
    ("Financial District", "North Beach"): 7,
    ("Financial District", "The Castro"): 23,
    ("Financial District", "Golden Gate Park"): 23,
    ("Russian Hill", "Financial District"): 11,
    ("Russian Hill", "Sunset District"): 23,
    ("Russian Hill", "North Beach"): 5,
    ("Russian Hill", "The Castro"): 21,
    ("Russian Hill", "Golden Gate Park"): 21,
    ("Sunset District", "Financial District"): 30,
    ("Sunset District", "Russian Hill"): 24,
    ("Sunset District", "North Beach"): 29,
    ("Sunset District", "The Castro"): 17,
    ("Sunset District", "Golden Gate Park"): 11,
    ("North Beach", "Financial District"): 8,
    ("North Beach", "Russian Hill"): 4,
    ("North Beach", "Sunset District"): 27,
    ("North Beach", "The Castro"): 22,
    ("North Beach", "Golden Gate Park"): 22,
    ("The Castro", "Financial District"): 20,
    ("The Castro", "Russian Hill"): 18,
    ("The Castro", "Sunset District"): 17,
    ("The Castro", "North Beach"): 20,
    ("The Castro", "Golden Gate Park"): 11,
    ("Golden Gate Park", "Financial District"): 26,
    ("Golden Gate Park", "Russian Hill"): 19,
    ("Golden Gate Park", "Sunset District"): 10,
    ("Golden Gate Park", "North Beach"): 24,
    ("Golden Gate Park", "The Castro"): 13,
}

# Meeting constraints
constraints = {
    "Ronald": {"location": "Russian Hill", "start": "13:45", "end": "17:15", "min_duration": 105},
    "Patricia": {"location": "Sunset District", "start": "09:15", "end": "22:00", "min_duration": 60},
    "Laura": {"location": "North Beach", "start": "12:30", "end": "12:45", "min_duration": 15},
    "Emily": {"location": "The Castro", "start": "16:15", "end": "18:30", "min_duration": 60},
    "Mary": {"location": "Golden Gate Park", "start": "15:00", "end": "16:30", "min_duration": 60},
}

# Meeting schedule
start_time = datetime.strptime("09:00", "%H:%M")

def convert_to_time_range(start, duration):
    start_dt = datetime.strptime(start, "%H:%M")
    end_dt = start_dt + timedelta(minutes=duration)
    return start_dt, end_dt

def format_time(dt):
    return dt.strftime("%H:%M")

def find_schedule():
    max_meetings = 0
    best_itinerary = []

    locations = list(constraints.keys())
    for perm in permutations(locations):
        current_time = start_time
        current_itinerary = []
        meeting_times = {}
        
        for person in perm:
            meeting_info = constraints[person]
            location = meeting_info["location"]
            start = meeting_info["start"]
            end = meeting_info["end"]
            min_duration = meeting_info["min_duration"]
            
            loc_start_dt, loc_end_dt = convert_to_time_range(start, 0)
            meet_duration = min_duration
            
            if location in meeting_times:
                loc_start_dt = max(loc_start_dt, meeting_times[location][1])
                
            if current_time < loc_start_dt:
                travel_time = travel_times.get((current_itinerary[-1]["location"], location)) if current_itinerary else 0
                arrive_time = current_time + timedelta(minutes=travel_time) if travel_time else current_time
                
                if arrive_time < loc_start_dt:
                    current_time = loc_start_dt
            
            travel_time = travel_times.get((current_itinerary[-1]["location"], location), 0) if current_itinerary else 0
            start_meeting_time = current_time + timedelta(minutes=travel_time)
            
            if start_meeting_time >= loc_start_dt and start_meeting_time + timedelta(minutes=meet_duration) <= loc_end_dt:
                end_meeting_time = start_meeting_time + timedelta(minutes=meet_duration)
                current_itinerary.append({
                    "action": "meet",
                    "location": location,
                    "person": person,
                    "start_time": format_time(start_meeting_time),
                    "end_time": format_time(end_meeting_time)
                })
                current_time = end_meeting_time
                meeting_times[location] = (start_meeting_time, end_meeting_time)
        
        if len(current_itinerary) > max_meetings:
            max_meetings = len(current_itinerary)
            best_itinerary = current_itinerary

    return best_itinerary

if __name__ == "__main__":
    itinerary = find_schedule()
    result = {"itinerary": itinerary}
    print(json.dumps(result, indent=2))