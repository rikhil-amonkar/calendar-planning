import json
from datetime import datetime, timedelta

# Define travel times
travel_times = {
    "Pacific Heights": {"Golden Gate Park": 15, "The Castro": 16, "Bayview": 22, "Marina District": 6, "Union Square": 12, "Sunset District": 21, "Alamo Square": 10, "Financial District": 13, "Mission District": 15},
    "Golden Gate Park": {"Pacific Heights": 16, "The Castro": 13, "Bayview": 23, "Marina District": 16, "Union Square": 22, "Sunset District": 10, "Alamo Square": 9, "Financial District": 26, "Mission District": 17},
    "The Castro": {"Pacific Heights": 16, "Golden Gate Park": 11, "Bayview": 19, "Marina District": 21, "Union Square": 19, "Sunset District": 17, "Alamo Square": 8, "Financial District": 21, "Mission District": 7},
    "Bayview": {"Pacific Heights": 23, "Golden Gate Park": 22, "The Castro": 19, "Marina District": 27, "Union Square": 18, "Sunset District": 23, "Alamo Square": 16, "Financial District": 19, "Mission District": 13},
    "Marina District": {"Pacific Heights": 6, "Golden Gate Park": 16, "The Castro": 21, "Bayview": 27, "Union Square": 16, "Sunset District": 19, "Alamo Square": 15, "Financial District": 17, "Mission District": 20},
    "Union Square": {"Pacific Heights": 12, "Golden Gate Park": 22, "The Castro": 17, "Bayview": 15, "Marina District": 16, "Sunset District": 27, "Alamo Square": 14, "Financial District": 9, "Mission District": 14},
    "Sunset District": {"Pacific Heights": 21, "Golden Gate Park": 10, "The Castro": 17, "Bayview": 22, "Marina District": 19, "Union Square": 27, "Alamo Square": 16, "Financial District": 30, "Mission District": 25},
    "Alamo Square": {"Pacific Heights": 10, "Golden Gate Park": 9, "The Castro": 8, "Bayview": 16, "Marina District": 15, "Union Square": 14, "Sunset District": 16, "Financial District": 17, "Mission District": 10},
    "Financial District": {"Pacific Heights": 13, "Golden Gate Park": 23, "The Castro": 20, "Bayview": 19, "Marina District": 15, "Union Square": 9, "Sunset District": 30, "Alamo Square": 17, "Mission District": 15},
    "Mission District": {"Pacific Heights": 15, "Golden Gate Park": 17, "The Castro": 7, "Bayview": 13, "Marina District": 19, "Union Square": 14, "Sunset District": 24, "Alamo Square": 10, "Financial District": 15}
}

# Define meeting constraints
constraints = {
    "Helen": {"location": "Golden Gate Park", "start": "9:30", "end": "12:15", "min_duration": 45},
    "Steven": {"location": "The Castro", "start": "20:15", "end": "22:00", "min_duration": 105},
    "Deborah": {"location": "Bayview", "start": "8:30", "end": "12:00", "min_duration": 30},
    "Matthew": {"location": "Marina District", "start": "9:15", "end": "14:15", "min_duration": 45},
    "Joseph": {"location": "Union Square", "start": "14:15", "end": "18:45", "min_duration": 120},
    "Ronald": {"location": "Sunset District", "start": "16:00", "end": "20:45", "min_duration": 60},
    "Robert": {"location": "Alamo Square", "start": "18:30", "end": "21:15", "min_duration": 120},
    "Rebecca": {"location": "Financial District", "start": "14:45", "end": "16:15", "min_duration": 30},
    "Elizabeth": {"location": "Mission District", "start": "18:30", "end": "21:00", "min_duration": 120}
}

def parse_time(time_str):
    return datetime.strptime(time_str, "%H:%M")

def format_time(time_obj):
    return time_obj.strftime("%H:%M")

def find_meeting_slot(constraint, current_time):
    start = parse_time(constraint["start"])
    end = parse_time(constraint["end"])
    min_duration = constraint["min_duration"]
    
    if current_time >= end:
        return None
    
    if current_time < start:
        current_time = start
    
    meeting_end = current_time + timedelta(minutes=min_duration)
    
    if meeting_end <= end:
        return current_time, meeting_end
    
    return None

def calculate_itinerary():
    current_location = "Pacific Heights"
    current_time = parse_time("9:00")
    itinerary = []
    
    # Sort constraints by start time
    sorted_constraints = sorted(constraints.items(), key=lambda x: parse_time(x[1]["start"]))
    
    for person, constraint in sorted_constraints:
        location = constraint["location"]
        
        # Calculate travel time
        travel_time = travel_times[current_location][location]
        next_time = current_time + timedelta(minutes=travel_time)
        
        # Find meeting slot
        slot = find_meeting_slot(constraint, next_time)
        if slot:
            start, end = slot
            itinerary.append({
                "action": "meet",
                "location": location,
                "person": person,
                "start_time": format_time(start),
                "end_time": format_time(end)
            })
            current_location = location
            current_time = end
    
    return itinerary

itinerary = calculate_itinerary()
result = {"itinerary": itinerary}
print(json.dumps(result))