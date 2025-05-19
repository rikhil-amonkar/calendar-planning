import json
from datetime import datetime, timedelta

# Define the travel times in minutes
travel_times = {
    ("Union Square", "Golden Gate Park"): 22,
    ("Union Square", "Pacific Heights"): 15,
    ("Union Square", "Presidio"): 24,
    ("Union Square", "Chinatown"): 7,
    ("Union Square", "The Castro"): 19,
    ("Golden Gate Park", "Union Square"): 22,
    ("Golden Gate Park", "Pacific Heights"): 16,
    ("Golden Gate Park", "Presidio"): 11,
    ("Golden Gate Park", "Chinatown"): 23,
    ("Golden Gate Park", "The Castro"): 13,
    ("Pacific Heights", "Union Square"): 12,
    ("Pacific Heights", "Golden Gate Park"): 15,
    ("Pacific Heights", "Presidio"): 11,
    ("Pacific Heights", "Chinatown"): 11,
    ("Pacific Heights", "The Castro"): 16,
    ("Presidio", "Union Square"): 22,
    ("Presidio", "Golden Gate Park"): 12,
    ("Presidio", "Pacific Heights"): 11,
    ("Presidio", "Chinatown"): 21,
    ("Presidio", "The Castro"): 21,
    ("Chinatown", "Union Square"): 7,
    ("Chinatown", "Golden Gate Park"): 23,
    ("Chinatown", "Pacific Heights"): 10,
    ("Chinatown", "Presidio"): 19,
    ("Chinatown", "The Castro"): 22,
    ("The Castro", "Union Square"): 19,
    ("The Castro", "Golden Gate Park"): 11,
    ("The Castro", "Pacific Heights"): 16,
    ("The Castro", "Presidio"): 20,
    ("The Castro", "Chinatown"): 20,
}

# Define the meeting constraints
meetings = {
    "Andrew": {"location": "Golden Gate Park", "start": "11:45", "end": "14:30", "min_duration": 75},
    "Sarah": {"location": "Pacific Heights", "start": "16:15", "end": "18:45", "min_duration": 15},
    "Nancy": {"location": "Presidio", "start": "17:30", "end": "19:15", "min_duration": 60},
    "Rebecca": {"location": "Chinatown", "start": "09:45", "end": "21:30", "min_duration": 90},
    "Robert": {"location": "The Castro", "start": "08:30", "end": "14:15", "min_duration": 30},
}

# Convert times to datetime objects
def time_to_datetime(time_str):
    return datetime.strptime(time_str, "%H:%M")

# Main meeting planner function
def schedule_meetings():
    start_of_day = time_to_datetime("09:00")
    end_of_day = time_to_datetime("21:30")
    
    itinerary = []
    current_time = start_of_day
    
    # Meeting with Rebecca initially, since she can meet earliest
    rebecca_start = max(current_time + timedelta(minutes=travel_times[("Union Square", "Chinatown")]), 
                        time_to_datetime(meetings["Rebecca"]["start"]))
    rebecca_end = rebecca_start + timedelta(minutes=meetings["Rebecca"]["min_duration"])
    
    if rebecca_end <= end_of_day:
        itinerary.append({
            "action": "meet",
            "location": "Chinatown",
            "person": "Rebecca",
            "start_time": rebecca_start.strftime("%H:%M"),
            "end_time": rebecca_end.strftime("%H:%M"),
        })
        current_time = rebecca_end + timedelta(minutes=travel_times[("Chinatown", "Golden Gate Park")])
    
    # Meeting with Andrew next
    andrew_start = max(current_time + timedelta(minutes=travel_times[("Union Square", "Golden Gate Park")]),
                       time_to_datetime(meetings["Andrew"]["start"]))
    andrew_end = andrew_start + timedelta(minutes=meetings["Andrew"]["min_duration"])
    
    if andrew_end <= time_to_datetime(meetings["Andrew"]["end"]) and \
            andrew_end <= end_of_day:
        itinerary.append({
            "action": "meet",
            "location": "Golden Gate Park",
            "person": "Andrew",
            "start_time": andrew_start.strftime("%H:%M"),
            "end_time": andrew_end.strftime("%H:%M"),
        })
        current_time = andrew_end + timedelta(minutes=travel_times[("Golden Gate Park", "Pacific Heights")])
    
    # Meeting with Sarah
    sarah_start = max(current_time + timedelta(minutes=travel_times[("Pacific Heights", "Pacific Heights")]), 
                      time_to_datetime(meetings["Sarah"]["start"]))
    sarah_end = sarah_start + timedelta(minutes=meetings["Sarah"]["min_duration"])
    
    if sarah_end <= end_of_day and sarah_end <= time_to_datetime(meetings["Sarah"]["end"]):
        itinerary.append({
            "action": "meet",
            "location": "Pacific Heights",
            "person": "Sarah",
            "start_time": sarah_start.strftime("%H:%M"),
            "end_time": sarah_end.strftime("%H:%M"),
        })
        current_time = sarah_end + timedelta(minutes=travel_times[("Pacific Heights", "Presidio")])
    
    # Meeting with Nancy last
    nancy_start = max(current_time + timedelta(minutes=travel_times[("Presidio", "Presidio")]), 
                      time_to_datetime(meetings["Nancy"]["start"]))
    nancy_end = nancy_start + timedelta(minutes=meetings["Nancy"]["min_duration"])
    
    if nancy_end <= end_of_day and nancy_end <= time_to_datetime(meetings["Nancy"]["end"]):
        itinerary.append({
            "action": "meet",
            "location": "Presidio",
            "person": "Nancy",
            "start_time": nancy_start.strftime("%H:%M"),
            "end_time": nancy_end.strftime("%H:%M"),
        })

    return {
        "itinerary": itinerary
    }

result = schedule_meetings()
print(json.dumps(result, indent=2))