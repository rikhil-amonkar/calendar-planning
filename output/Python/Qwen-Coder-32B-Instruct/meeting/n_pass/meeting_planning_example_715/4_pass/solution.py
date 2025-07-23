import json
from datetime import datetime, timedelta

# Define travel times
travel_times = {
    "Presidio": {"Marina District": 11, "The Castro": 21, "Fisherman's Wharf": 19, "Bayview": 31, "Pacific Heights": 11, "Mission District": 26, "Alamo Square": 19, "Golden Gate Park": 12},
    "Marina District": {"Presidio": 10, "The Castro": 22, "Fisherman's Wharf": 10, "Bayview": 27, "Pacific Heights": 7, "Mission District": 20, "Alamo Square": 15, "Golden Gate Park": 18},
    "The Castro": {"Presidio": 20, "Marina District": 21, "Fisherman's Wharf": 24, "Bayview": 19, "Pacific Heights": 16, "Mission District": 7, "Alamo Square": 8, "Golden Gate Park": 11},
    "Fisherman's Wharf": {"Presidio": 17, "Marina District": 9, "The Castro": 27, "Bayview": 26, "Pacific Heights": 12, "Mission District": 22, "Alamo Square": 21, "Golden Gate Park": 25},
    "Bayview": {"Presidio": 32, "Marina District": 27, "The Castro": 19, "Fisherman's Wharf": 25, "Pacific Heights": 23, "Mission District": 13, "Alamo Square": 16, "Golden Gate Park": 22},
    "Pacific Heights": {"Presidio": 11, "Marina District": 6, "The Castro": 16, "Fisherman's Wharf": 13, "Bayview": 22, "Mission District": 15, "Alamo Square": 10, "Golden Gate Park": 15},
    "Mission District": {"Presidio": 25, "Marina District": 19, "The Castro": 7, "Fisherman's Wharf": 22, "Bayview": 14, "Pacific Heights": 16, "Alamo Square": 11, "Golden Gate Park": 17},
    "Alamo Square": {"Presidio": 17, "Marina District": 15, "The Castro": 8, "Fisherman's Wharf": 19, "Bayview": 16, "Pacific Heights": 10, "Mission District": 10, "Golden Gate Park": 9},
    "Golden Gate Park": {"Presidio": 11, "Marina District": 16, "The Castro": 13, "Fisherman's Wharf": 24, "Bayview": 23, "Pacific Heights": 16, "Mission District": 17, "Alamo Square": 9}
}

# Define meeting constraints
constraints = {
    "Amanda": {"location": "Marina District", "start": "14:45", "end": "19:30", "min_duration": 105},
    "Melissa": {"location": "The Castro", "start": "09:30", "end": "17:00", "min_duration": 30},
    "Jeffrey": {"location": "Fisherman's Wharf", "start": "12:45", "end": "18:45", "min_duration": 120},
    "Matthew": {"location": "Bayview", "start": "10:15", "end": "13:15", "min_duration": 30},
    "Nancy": {"location": "Pacific Heights", "start": "17:00", "end": "21:30", "min_duration": 105},
    "Karen": {"location": "Mission District", "start": "17:30", "end": "20:30", "min_duration": 105},
    "Robert": {"location": "Alamo Square", "start": "11:15", "end": "17:30", "min_duration": 120},
    "Joseph": {"location": "Golden Gate Park", "start": "08:30", "end": "21:15", "min_duration": 105}
}

def time_to_minutes(time_str):
    h, m = map(int, time_str.split(':'))
    return h * 60 + m

def minutes_to_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02}"

def can_meet(start, end, min_duration):
    return time_to_minutes(end) - time_to_minutes(start) >= min_duration

def find_optimal_schedule():
    start_time = "09:00"
    current_location = "Presidio"
    current_time = time_to_minutes(start_time)
    itinerary = []

    # Sort constraints by start time
    sorted_constraints = sorted(constraints.items(), key=lambda x: time_to_minutes(x[1]["start"]))

    for person, details in sorted_constraints:
        location = details["location"]
        start = details["start"]
        end = details["end"]
        min_duration = details["min_duration"]

        # Calculate travel time
        travel_time = travel_times[current_location][location]

        # Calculate potential meeting start time
        potential_start = max(current_time + travel_time, time_to_minutes(start))

        # Calculate potential meeting end time
        potential_end = potential_start + min_duration

        # Check if the potential meeting fits within the person's available window
        if potential_end <= time_to_minutes(end):
            itinerary.append({
                "action": "meet",
                "location": location,
                "person": person,
                "start_time": minutes_to_time(potential_start),
                "end_time": minutes_to_time(potential_end)
            })
            current_time = potential_end
            current_location = location
        else:
            # If we can't meet for the required duration, skip this person
            continue

    return itinerary

itinerary = find_optimal_schedule()
result = {"itinerary": itinerary}
print(json.dumps(result, indent=2))