import json
from datetime import datetime, timedelta
import itertools

# Travel times in minutes
travel_times = {
    ("Haight-Ashbury", "Russian Hill"): 17,
    ("Haight-Ashbury", "Fisherman's Wharf"): 23,
    ("Haight-Ashbury", "Nob Hill"): 15,
    ("Haight-Ashbury", "Golden Gate Park"): 7,
    ("Haight-Ashbury", "Alamo Square"): 5,
    ("Haight-Ashbury", "Pacific Heights"): 12,
    ("Russian Hill", "Haight-Ashbury"): 17,
    ("Russian Hill", "Fisherman's Wharf"): 7,
    ("Russian Hill", "Nob Hill"): 5,
    ("Russian Hill", "Golden Gate Park"): 21,
    ("Russian Hill", "Alamo Square"): 15,
    ("Russian Hill", "Pacific Heights"): 7,
    ("Fisherman's Wharf", "Haight-Ashbury"): 22,
    ("Fisherman's Wharf", "Russian Hill"): 7,
    ("Fisherman's Wharf", "Nob Hill"): 11,
    ("Fisherman's Wharf", "Golden Gate Park"): 25,
    ("Fisherman's Wharf", "Alamo Square"): 20,
    ("Fisherman's Wharf", "Pacific Heights"): 12,
    ("Nob Hill", "Haight-Ashbury"): 13,
    ("Nob Hill", "Russian Hill"): 5,
    ("Nob Hill", "Fisherman's Wharf"): 11,
    ("Nob Hill", "Golden Gate Park"): 17,
    ("Nob Hill", "Alamo Square"): 11,
    ("Nob Hill", "Pacific Heights"): 8,
    ("Golden Gate Park", "Haight-Ashbury"): 7,
    ("Golden Gate Park", "Russian Hill"): 19,
    ("Golden Gate Park", "Fisherman's Wharf"): 24,
    ("Golden Gate Park", "Nob Hill"): 20,
    ("Golden Gate Park", "Alamo Square"): 10,
    ("Golden Gate Park", "Pacific Heights"): 16,
    ("Alamo Square", "Haight-Ashbury"): 5,
    ("Alamo Square", "Russian Hill"): 13,
    ("Alamo Square", "Fisherman's Wharf"): 19,
    ("Alamo Square", "Nob Hill"): 11,
    ("Alamo Square", "Golden Gate Park"): 9,
    ("Alamo Square", "Pacific Heights"): 10,
    ("Pacific Heights", "Haight-Ashbury"): 11,
    ("Pacific Heights", "Russian Hill"): 7,
    ("Pacific Heights", "Fisherman's Wharf"): 13,
    ("Pacific Heights", "Nob Hill"): 8,
    ("Pacific Heights", "Golden Gate Park"): 15,
    ("Pacific Heights", "Alamo Square"): 10,
}

# Meeting constraints
meetings = {
    "Stephanie": {
        "location": "Russian Hill",
        "start": "20:00",
        "end": "20:45",
        "duration": 15,
    },
    "Kevin": {
        "location": "Fisherman's Wharf",
        "start": "19:15",
        "end": "21:45",
        "duration": 75,
    },
    "Robert": {
        "location": "Nob Hill",
        "start": "07:45",
        "end": "10:30",
        "duration": 90,
    },
    "Steven": {
        "location": "Golden Gate Park",
        "start": "08:30",
        "end": "17:00",
        "duration": 75,
    },
    "Anthony": {
        "location": "Alamo Square",
        "start": "07:45",
        "end": "19:45",
        "duration": 15,
    },
    "Sandra": {
        "location": "Pacific Heights",
        "start": "14:45",
        "end": "21:45",
        "duration": 45,
    },
}

# Convert time string to datetime
def parse_time(time_str):
    return datetime.strptime(time_str, "%H:%M")

# Convert datetime to string
def format_time(dt):
    return dt.strftime("%H:%M")

def compute_schedule():
    start_time = parse_time("09:00")
    itinerary = []
    
    def can_meet(start, end, duration):
        return (end - start).total_seconds() / 60 >= duration
    
    # Try to meet all friends in a feasible order
    locations = ["Haight-Ashbury", "Russian Hill", "Fisherman's Wharf", "Nob Hill", 
                 "Golden Gate Park", "Alamo Square", "Pacific Heights"]
    
    # Generate all permutations of locations to attempt
    for order in itertools.permutations(locations[1:]):  # excluding "Haight-Ashbury"
        current_time = start_time
        current_location = "Haight-Ashbury"
        temp_itinerary = []
        
        for friend in order:
            meeting_info = meetings[friend]
            travel_time = travel_times[(current_location, meeting_info['location'])]
            arrival_time = current_time + timedelta(minutes=travel_time)
            meeting_start = max(arrival_time, parse_time(meeting_info['start']))
            meeting_end = meeting_start + timedelta(minutes=meeting_info['duration'])
            
            if can_meet(meeting_start, parse_time(meeting_info['end']), meeting_info['duration']):
                temp_itinerary.append({
                    "action": "meet",
                    "location": meeting_info['location'],
                    "person": friend,
                    "start_time": format_time(meeting_start),
                    "end_time": format_time(meeting_end),
                })
                current_time = meeting_end
                current_location = meeting_info['location']
            else:
                break  # can't meet this friend in this order
        
        if len(temp_itinerary) == len(order):
            itinerary = temp_itinerary
            break  # found a complete valid itinerary
    
    return {"itinerary": itinerary}

result = compute_schedule()
print(json.dumps(result, indent=2))