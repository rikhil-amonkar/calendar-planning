import json
from datetime import datetime, timedelta

# Travel distances (in minutes)
travel_times = {
    "Haight-Ashbury": {
        "Russian Hill": 17,
        "Fisherman's Wharf": 23,
        "Nob Hill": 15,
        "Golden Gate Park": 7,
        "Alamo Square": 5,
        "Pacific Heights": 12
    },
    "Russian Hill": {
        "Haight-Ashbury": 17,
        "Fisherman's Wharf": 7,
        "Nob Hill": 5,
        "Golden Gate Park": 21,
        "Alamo Square": 15,
        "Pacific Heights": 7
    },
    "Fisherman's Wharf": {
        "Haight-Ashbury": 22,
        "Russian Hill": 7,
        "Nob Hill": 11,
        "Golden Gate Park": 25,
        "Alamo Square": 20,
        "Pacific Heights": 12
    },
    "Nob Hill": {
        "Haight-Ashbury": 13,
        "Russian Hill": 5,
        "Fisherman's Wharf": 11,
        "Golden Gate Park": 17,
        "Alamo Square": 11,
        "Pacific Heights": 8
    },
    "Golden Gate Park": {
        "Haight-Ashbury": 7,
        "Russian Hill": 19,
        "Fisherman's Wharf": 24,
        "Nob Hill": 20,
        "Alamo Square": 10,
        "Pacific Heights": 16
    },
    "Alamo Square": {
        "Haight-Ashbury": 5,
        "Russian Hill": 13,
        "Fisherman's Wharf": 19,
        "Nob Hill": 11,
        "Golden Gate Park": 9,
        "Pacific Heights": 10
    },
    "Pacific Heights": {
        "Haight-Ashbury": 11,
        "Russian Hill": 7,
        "Fisherman's Wharf": 13,
        "Nob Hill": 8,
        "Golden Gate Park": 15,
        "Alamo Square": 10
    }
}

# Constraints
constraints = {
    "Stephanie": {"start_time": "20:00", "end_time": "20:45", "min_time": 15},
    "Kevin": {"start_time": "19:15", "end_time": "21:45", "min_time": 75},
    "Robert": {"start_time": "07:45", "end_time": "10:30", "min_time": 90},
    "Steven": {"start_time": "08:30", "end_time": "17:00", "min_time": 75},
    "Anthony": {"start_time": "07:45", "end_time": "19:45", "min_time": 15},
    "Sandra": {"start_time": "14:45", "end_time": "19:45", "min_time": 45}
}

# Initial location and time
initial_location = "Haight-Ashbury"
initial_time = datetime.strptime("09:00", "%H:%M")

# Initialize itinerary
itinerary = []

def compute_travel_time(location1, location2):
    return travel_times[location1][location2]

def is_available(person, meet_time):
    start_time = datetime.strptime(constraints[person]["start_time"], "%H:%M")
    end_time = datetime.strptime(constraints[person]["end_time"], "%H:%M")
    min_time = start_time + timedelta(minutes=constraints[person]["min_time"])
    
    return start_time <= meet_time <= end_time and meet_time >= min_time

def compute_schedule():
    global itinerary
    current_location = initial_location
    current_time = initial_time

    for person in constraints:
        start_time = datetime.strptime(constraints[person]["start_time"], "%H:%M")
        end_time = datetime.strptime(constraints[person]["end_time"], "%H:%M")
        min_time = start_time + timedelta(minutes=constraints[person]["min_time"])
        
        if start_time <= end_time and min_time <= end_time:
            available_times = []
            for i in range((start_time - initial_time).total_seconds() // 60, (end_time - initial_time).total_seconds() // 60):
                meet_time = initial_time + timedelta(minutes=i)
                if is_available(person, meet_time):
                    available_times.append(meet_time)
            
            if available_times:
                meet_time = min(available_times)
                travel_time = compute_travel_time(current_location, constraints[person]["start_time"][:2])
                meet_time += timedelta(minutes=travel_time)
                itinerary.append({"action": "meet", "location": constraints[person]["start_time"][:2], "person": person, "start_time": meet_time.strftime("%H:%M"), "end_time": (meet_time + timedelta(minutes=constraints[person]["min_time"])).strftime("%H:%M")})
                current_time = meet_time + timedelta(minutes=constraints[person]["min_time"])
                current_location = constraints[person]["start_time"][:2]

    return itinerary

schedule = compute_schedule()
print(json.dumps({"itinerary": schedule}, indent=4))