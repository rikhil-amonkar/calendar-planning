import json
from datetime import datetime, timedelta

# Define travel times (in minutes)
travel_times = {
    ("Financial District", "Fisherman's Wharf"): 10,
    ("Financial District", "Pacific Heights"): 13,
    ("Financial District", "Mission District"): 17,
    ("Fisherman's Wharf", "Financial District"): 11,
    ("Fisherman's Wharf", "Pacific Heights"): 12,
    ("Fisherman's Wharf", "Mission District"): 22,
    ("Pacific Heights", "Financial District"): 13,
    ("Pacific Heights", "Fisherman's Wharf"): 13,
    ("Pacific Heights", "Mission District"): 15,
    ("Mission District", "Financial District"): 17,
    ("Mission District", "Fisherman's Wharf"): 22,
    ("Mission District", "Pacific Heights"): 16,
}

# Define constraints
constraints = {
    "David": {"location": "Fisherman's Wharf", "start": "10:45", "end": "15:30", "duration": 15},
    "Timothy": {"location": "Pacific Heights", "start": "9:00", "end": "15:30", "duration": 75},
    "Robert": {"location": "Mission District", "start": "12:15", "end": "19:45", "duration": 90},
}

# Convert time strings to datetime objects for easier manipulation
def str_to_time(s):
    return datetime.strptime(s, '%H:%M')

# Travel and meeting scheduling logic
def compute_schedule():
    itinerary = []
    
    # Start at Financial District at 9:00
    current_time = str_to_time("9:00")
    
    # Meet Timothy at Pacific Heights
    travel_time = travel_times[("Financial District", "Pacific Heights")]
    arrive_time = current_time + timedelta(minutes=travel_time)
    
    if arrive_time <= str_to_time(constraints["Timothy"]["end"]):
        meeting_start = max(arrive_time, str_to_time(constraints["Timothy"]["start"]))
        meeting_end = meeting_start + timedelta(minutes=constraints["Timothy"]["duration"])
        
        if meeting_end <= str_to_time(constraints["Timothy"]["end"]):
            itinerary.append({
                "action": "meet",
                "location": constraints["Timothy"]["location"],
                "person": "Timothy",
                "start_time": meeting_start.strftime('%H:%M'),
                "end_time": meeting_end.strftime('%H:%M')
            })
            current_time = meeting_end + timedelta(minutes=travel_time)  # Travel time back
    
    # Meet David at Fisherman's Wharf
    travel_time = travel_times[("Financial District", "Fisherman's Wharf")]
    arrive_time = current_time + timedelta(minutes=travel_time)
    
    if arrive_time <= str_to_time(constraints["David"]["end"]):
        meeting_start = max(arrive_time, str_to_time(constraints["David"]["start"]))
        meeting_end = meeting_start + timedelta(minutes=constraints["David"]["duration"])
        
        if meeting_end <= str_to_time(constraints["David"]["end"]):
            itinerary.append({
                "action": "meet",
                "location": constraints["David"]["location"],
                "person": "David",
                "start_time": meeting_start.strftime('%H:%M'),
                "end_time": meeting_end.strftime('%H:%M')
            })
            current_time = meeting_end + timedelta(minutes=travel_time)  # Travel time back
    
    # Meet Robert at Mission District
    travel_time = travel_times[("Financial District", "Mission District")]
    arrive_time = current_time + timedelta(minutes=travel_time)

    if arrive_time <= str_to_time(constraints["Robert"]["end"]):
        meeting_start = max(arrive_time, str_to_time(constraints["Robert"]["start"]))
        meeting_end = meeting_start + timedelta(minutes=constraints["Robert"]["duration"])

        if meeting_end <= str_to_time(constraints["Robert"]["end"]):
            itinerary.append({
                "action": "meet",
                "location": constraints["Robert"]["location"],
                "person": "Robert",
                "start_time": meeting_start.strftime('%H:%M'),
                "end_time": meeting_end.strftime('%H:%M')
            })
    
    return {"itinerary": itinerary}

# Execute the meeting schedule computation
schedule = compute_schedule()
print(json.dumps(schedule, indent=2))