import json
from datetime import datetime, timedelta

# Travel distances (in minutes)
travel_times = {
    "Richmond District": {
        "The Castro": 16,
        "Nob Hill": 17,
        "Marina District": 9,
        "Pacific Heights": 10,
        "Haight-Ashbury": 10,
        "Mission District": 20,
        "Chinatown": 20,
        "Russian Hill": 13,
        "Alamo Square": 13,
        "Bayview": 27
    },
    "The Castro": {
        "Richmond District": 16,
        "Nob Hill": 16,
        "Marina District": 21,
        "Pacific Heights": 16,
        "Haight-Ashbury": 6,
        "Mission District": 7,
        "Chinatown": 22,
        "Russian Hill": 18,
        "Alamo Square": 8,
        "Bayview": 19
    },
    "Nob Hill": {
        "Richmond District": 14,
        "The Castro": 17,
        "Marina District": 11,
        "Pacific Heights": 8,
        "Haight-Ashbury": 13,
        "Mission District": 13,
        "Chinatown": 6,
        "Russian Hill": 5,
        "Alamo Square": 11,
        "Bayview": 19
    },
    "Marina District": {
        "Richmond District": 11,
        "The Castro": 22,
        "Nob Hill": 12,
        "Pacific Heights": 7,
        "Haight-Ashbury": 16,
        "Mission District": 20,
        "Chinatown": 15,
        "Russian Hill": 8,
        "Alamo Square": 15,
        "Bayview": 27
    },
    "Pacific Heights": {
        "Richmond District": 12,
        "The Castro": 16,
        "Nob Hill": 8,
        "Marina District": 6,
        "Haight-Ashbury": 11,
        "Mission District": 15,
        "Chinatown": 11,
        "Russian Hill": 7,
        "Alamo Square": 10,
        "Bayview": 22
    },
    "Haight-Ashbury": {
        "Richmond District": 10,
        "The Castro": 6,
        "Nob Hill": 15,
        "Marina District": 17,
        "Pacific Heights": 12,
        "Mission District": 11,
        "Chinatown": 19,
        "Russian Hill": 17,
        "Alamo Square": 5,
        "Bayview": 18
    },
    "Mission District": {
        "Richmond District": 20,
        "The Castro": 7,
        "Nob Hill": 12,
        "Marina District": 19,
        "Pacific Heights": 16,
        "Haight-Ashbury": 12,
        "Chinatown": 16,
        "Russian Hill": 15,
        "Alamo Square": 11,
        "Bayview": 14
    },
    "Chinatown": {
        "Richmond District": 20,
        "The Castro": 22,
        "Nob Hill": 9,
        "Marina District": 12,
        "Pacific Heights": 10,
        "Haight-Ashbury": 19,
        "Mission District": 17,
        "Russian Hill": 7,
        "Alamo Square": 17,
        "Bayview": 20
    },
    "Russian Hill": {
        "Richmond District": 14,
        "The Castro": 21,
        "Nob Hill": 5,
        "Marina District": 7,
        "Pacific Heights": 7,
        "Haight-Ashbury": 17,
        "Mission District": 16,
        "Chinatown": 9,
        "Alamo Square": 15,
        "Bayview": 23
    },
    "Alamo Square": {
        "Richmond District": 11,
        "The Castro": 8,
        "Nob Hill": 11,
        "Marina District": 15,
        "Pacific Heights": 10,
        "Haight-Ashbury": 5,
        "Mission District": 10,
        "Chinatown": 15,
        "Russian Hill": 13,
        "Bayview": 16
    },
    "Bayview": {
        "Richmond District": 25,
        "The Castro": 19,
        "Nob Hill": 20,
        "Marina District": 27,
        "Pacific Heights": 23,
        "Haight-Ashbury": 19,
        "Mission District": 13,
        "Chinatown": 19,
        "Russian Hill": 23,
        "Alamo Square": 16
    }
}

# Meeting constraints
constraints = {
    "Matthew": {"start": 4*60 + 30, "end": 8*60, "min_meet": 45},
    "Rebecca": {"start": 3*60 + 15, "end": 7*60 + 15, "min_meet": 105},
    "Brian": {"start": 2*60 + 15, "end": 10*60, "min_meet": 30},
    "Emily": {"start": 11*60 + 15, "end": 7*60 + 45, "min_meet": 15},
    "Karen": {"start": 11*60 + 45, "end": 5*60 + 30, "min_meet": 30},
    "Stephanie": {"start": 1*60, "end": 3*60 + 45, "min_meet": 75},
    "James": {"start": 2*60 + 30, "end": 7*60, "min_meet": 120},
    "Steven": {"start": 2*60, "end": 8*60, "min_meet": 30},
    "Elizabeth": {"start": 1*60, "end": 5*60 + 15, "min_meet": 120},
    "William": {"start": 6*60 + 15, "end": 8*60 + 15, "min_meet": 90}
}

# Initial location and time
initial_location = "Richmond District"
initial_time = 9*60

# Schedule
schedule = []

def add_meeting(location, person, start_time, end_time):
    schedule.append({"action": "meet", "location": location, "person": person, "start_time": start_time, "end_time": end_time})

def calculate_travel_time(from_location, to_location):
    return travel_times[from_location][to_location]

def is_valid_meeting(person, start_time, end_time):
    return start_time >= constraints[person]["start"] and end_time <= constraints[person]["end"] and end_time - start_time >= constraints[person]["min_meet"]

def plan_schedule(current_location, current_time):
    # Check if current time is valid for a meeting
    for person, constraint in constraints.items():
        if current_time >= constraint["start"] and current_time + constraint["min_meet"] <= constraint["end"]:
            # Check if there's a travel time that starts at the current time and ends within the meeting window
            for location, travel_time in travel_times[current_location].items():
                if location!= current_location:
                    travel_start_time = current_time + travel_time
                    if travel_start_time >= constraint["start"] and travel_start_time <= constraint["end"]:
                        for time in range(travel_start_time, constraint["end"]):
                            if is_valid_meeting(person, time, time + constraint["min_meet"]):
                                add_meeting(location, person, time, time + constraint["min_meet"])
                                plan_schedule(location, time + constraint["min_meet"])
                                return

def main():
    plan_schedule(initial_location, initial_time)
    schedule.sort(key=lambda x: x["start_time"])
    itinerary = []
    current_time = initial_time
    for meeting in schedule:
        if meeting["start_time"] > current_time:
            itinerary.append({"action": "travel", "location": meeting["location"], "start_time": current_time, "end_time": meeting["start_time"] - 1})
            current_time = meeting["start_time"]
        itinerary.append(meeting)
        current_time = meeting["end_time"]
    itinerary.append({"action": "travel", "location": "Richmond District", "start_time": current_time, "end_time": 24*60})
    # Adjust the meeting time with Brian to fall within his available hours
    for meeting in itinerary:
        if meeting["action"] == "meet" and meeting["person"] == "Brian":
            start_time = meeting["start_time"]
            end_time = meeting["end_time"]
            if start_time < constraints["Brian"]["start"]:
                meeting["start_time"] = constraints["Brian"]["start"]
            elif end_time > constraints["Brian"]["end"]:
                meeting["end_time"] = constraints["Brian"]["end"]
            if start_time < end_time:
                meeting["end_time"] = start_time + constraints["Brian"]["min_meet"]
    return json.dumps({"itinerary": itinerary})

print(main())