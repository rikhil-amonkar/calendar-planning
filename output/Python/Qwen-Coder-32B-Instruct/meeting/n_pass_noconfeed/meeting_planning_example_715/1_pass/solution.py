import json
from datetime import datetime, timedelta

# Define travel times
travel_times = {
    ("Presidio", "Marina District"): 11,
    ("Presidio", "The Castro"): 21,
    ("Presidio", "Fisherman's Wharf"): 19,
    ("Presidio", "Bayview"): 31,
    ("Presidio", "Pacific Heights"): 11,
    ("Presidio", "Mission District"): 26,
    ("Presidio", "Alamo Square"): 19,
    ("Presidio", "Golden Gate Park"): 12,
    ("Marina District", "Presidio"): 10,
    ("Marina District", "The Castro"): 22,
    ("Marina District", "Fisherman's Wharf"): 10,
    ("Marina District", "Bayview"): 27,
    ("Marina District", "Pacific Heights"): 7,
    ("Marina District", "Mission District"): 20,
    ("Marina District", "Alamo Square"): 15,
    ("Marina District", "Golden Gate Park"): 18,
    ("The Castro", "Presidio"): 20,
    ("The Castro", "Marina District"): 21,
    ("The Castro", "Fisherman's Wharf"): 24,
    ("The Castro", "Bayview"): 19,
    ("The Castro", "Pacific Heights"): 16,
    ("The Castro", "Mission District"): 7,
    ("The Castro", "Alamo Square"): 8,
    ("The Castro", "Golden Gate Park"): 11,
    ("Fisherman's Wharf", "Presidio"): 17,
    ("Fisherman's Wharf", "Marina District"): 9,
    ("Fisherman's Wharf", "The Castro"): 27,
    ("Fisherman's Wharf", "Bayview"): 26,
    ("Fisherman's Wharf", "Pacific Heights"): 12,
    ("Fisherman's Wharf", "Mission District"): 22,
    ("Fisherman's Wharf", "Alamo Square"): 21,
    ("Fisherman's Wharf", "Golden Gate Park"): 25,
    ("Bayview", "Presidio"): 32,
    ("Bayview", "Marina District"): 27,
    ("Bayview", "The Castro"): 19,
    ("Bayview", "Fisherman's Wharf"): 25,
    ("Bayview", "Pacific Heights"): 23,
    ("Bayview", "Mission District"): 13,
    ("Bayview", "Alamo Square"): 16,
    ("Bayview", "Golden Gate Park"): 22,
    ("Pacific Heights", "Presidio"): 11,
    ("Pacific Heights", "Marina District"): 6,
    ("Pacific Heights", "The Castro"): 16,
    ("Pacific Heights", "Fisherman's Wharf"): 13,
    ("Pacific Heights", "Bayview"): 22,
    ("Pacific Heights", "Mission District"): 15,
    ("Pacific Heights", "Alamo Square"): 10,
    ("Pacific Heights", "Golden Gate Park"): 15,
    ("Mission District", "Presidio"): 25,
    ("Mission District", "Marina District"): 19,
    ("Mission District", "The Castro"): 7,
    ("Mission District", "Fisherman's Wharf"): 22,
    ("Mission District", "Bayview"): 14,
    ("Mission District", "Pacific Heights"): 16,
    ("Mission District", "Alamo Square"): 11,
    ("Mission District", "Golden Gate Park"): 17,
    ("Alamo Square", "Presidio"): 17,
    ("Alamo Square", "Marina District"): 15,
    ("Alamo Square", "The Castro"): 8,
    ("Alamo Square", "Fisherman's Wharf"): 19,
    ("Alamo Square", "Bayview"): 16,
    ("Alamo Square", "Pacific Heights"): 10,
    ("Alamo Square", "Mission District"): 10,
    ("Alamo Square", "Golden Gate Park"): 9,
    ("Golden Gate Park", "Presidio"): 11,
    ("Golden Gate Park", "Marina District"): 16,
    ("Golden Gate Park", "The Castro"): 13,
    ("Golden Gate Park", "Fisherman's Wharf"): 24,
    ("Golden Gate Park", "Bayview"): 23,
    ("Golden Gate Park", "Pacific Heights"): 16,
    ("Golden Gate Park", "Mission District"): 17,
    ("Golden Gate Park", "Alamo Square"): 9,
}

# Define meeting constraints
meetings = {
    "Amanda": {"location": "Marina District", "start": "14:45", "end": "19:30", "min_duration": 105},
    "Melissa": {"location": "The Castro", "start": "09:30", "end": "17:00", "min_duration": 30},
    "Jeffrey": {"location": "Fisherman's Wharf", "start": "12:45", "end": "18:45", "min_duration": 120},
    "Matthew": {"location": "Bayview", "start": "10:15", "end": "13:15", "min_duration": 30},
    "Nancy": {"location": "Pacific Heights", "start": "17:00", "end": "21:30", "min_duration": 105},
    "Karen": {"location": "Mission District", "start": "17:30", "end": "20:30", "min_duration": 105},
    "Robert": {"location": "Alamo Square", "start": "11:15", "end": "17:30", "min_duration": 120},
    "Joseph": {"location": "Golden Gate Park", "start": "08:30", "end": "21:15", "min_duration": 105},
}

def parse_time(time_str):
    return datetime.strptime(time_str, "%H:%M")

def format_time(time_obj):
    return time_obj.strftime("%H:%M")

def can_meet(start, end, min_duration):
    return (end - start).total_seconds() / 60 >= min_duration

def find_best_schedule():
    start_time = parse_time("09:00")
    current_location = "Presidio"
    itinerary = []

    def try_meeting(person, location, start, end, min_duration):
        nonlocal start_time, current_location, itinerary
        travel_time = travel_times.get((current_location, location), float('inf'))
        arrival_time = start_time + timedelta(minutes=travel_time)
        if arrival_time < start:
            arrival_time = start
        leave_time = arrival_time + timedelta(minutes=min_duration)
        if leave_time <= end:
            itinerary.append({
                "action": "meet",
                "location": location,
                "person": person,
                "start_time": format_time(arrival_time),
                "end_time": format_time(leave_time)
            })
            start_time = leave_time
            current_location = location

    # Try to meet people in order of their availability
    for person, details in meetings.items():
        try_meeting(person, details["location"], parse_time(details["start"]), parse_time(details["end"]), details["min_duration"])

    return itinerary

itinerary = find_best_schedule()
solution = {"itinerary": itinerary}
print(json.dumps(solution))