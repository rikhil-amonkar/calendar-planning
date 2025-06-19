import json
from datetime import datetime, timedelta

# Travel distances (in minutes)
travel_distances = {
    "Union Square": {
        "The Castro": 19,
        "North Beach": 7,
        "Embarcadero": 10,
        "Alamo Square": 14,
        "Nob Hill": 7,
        "Presidio": 22,
        "Fisherman's Wharf": 13,
        "Mission District": 15,
        "Haight-Ashbury": 19
    },
    "The Castro": {
        "Union Square": 19,
        "North Beach": 23,
        "Embarcadero": 25,
        "Alamo Square": 8,
        "Nob Hill": 17,
        "Presidio": 21,
        "Fisherman's Wharf": 27,
        "Mission District": 7,
        "Haight-Ashbury": 6
    },
    "North Beach": {
        "Union Square": 7,
        "The Castro": 23,
        "Embarcadero": 5,
        "Alamo Square": 15,
        "Nob Hill": 8,
        "Presidio": 18,
        "Fisherman's Wharf": 6,
        "Mission District": 18,
        "Haight-Ashbury": 19
    },
    "Embarcadero": {
        "Union Square": 10,
        "The Castro": 25,
        "North Beach": 5,
        "Alamo Square": 16,
        "Nob Hill": 9,
        "Presidio": 20,
        "Fisherman's Wharf": 8,
        "Mission District": 20,
        "Haight-Ashbury": 21
    },
    "Alamo Square": {
        "Union Square": 14,
        "The Castro": 8,
        "North Beach": 15,
        "Embarcadero": 16,
        "Nob Hill": 11,
        "Presidio": 19,
        "Fisherman's Wharf": 21,
        "Mission District": 10,
        "Haight-Ashbury": 5
    },
    "Nob Hill": {
        "Union Square": 7,
        "The Castro": 17,
        "North Beach": 8,
        "Embarcadero": 9,
        "Alamo Square": 11,
        "Presidio": 18,
        "Fisherman's Wharf": 11,
        "Mission District": 13,
        "Haight-Ashbury": 13
    },
    "Presidio": {
        "Union Square": 22,
        "The Castro": 21,
        "North Beach": 18,
        "Embarcadero": 20,
        "Alamo Square": 19,
        "Nob Hill": 18,
        "Fisherman's Wharf": 19,
        "Mission District": 26,
        "Haight-Ashbury": 15
    },
    "Fisherman's Wharf": {
        "Union Square": 13,
        "The Castro": 27,
        "North Beach": 6,
        "Embarcadero": 8,
        "Alamo Square": 21,
        "Nob Hill": 11,
        "Presidio": 17,
        "Mission District": 22,
        "Haight-Ashbury": 22
    },
    "Mission District": {
        "Union Square": 15,
        "The Castro": 7,
        "North Beach": 17,
        "Embarcadero": 19,
        "Alamo Square": 11,
        "Nob Hill": 12,
        "Presidio": 25,
        "Fisherman's Wharf": 22,
        "Haight-Ashbury": 12
    },
    "Haight-Ashbury": {
        "Union Square": 19,
        "The Castro": 6,
        "North Beach": 19,
        "Embarcadero": 20,
        "Alamo Square": 5,
        "Nob Hill": 15,
        "Presidio": 15,
        "Fisherman's Wharf": 23,
        "Mission District": 11
    }
}

# Meeting constraints
constraints = {
    "Melissa": {
        "start_time": datetime(2024, 7, 26, 20, 15),
        "end_time": datetime(2024, 7, 26, 21, 15),
        "min_duration": 30
    },
    "Kimberly": {
        "start_time": datetime(2024, 7, 26, 7, 0),
        "end_time": datetime(2024, 7, 26, 10, 30),
        "min_duration": 15
    },
    "Joseph": {
        "start_time": datetime(2024, 7, 26, 15, 30),
        "end_time": datetime(2024, 7, 26, 19, 30),
        "min_duration": 75
    },
    "Barbara": {
        "start_time": datetime(2024, 7, 26, 20, 45),
        "end_time": datetime(2024, 7, 26, 21, 45),
        "min_duration": 15
    },
    "Kenneth": {
        "start_time": datetime(2024, 7, 26, 12, 15),
        "end_time": datetime(2024, 7, 26, 17, 15),
        "min_duration": 105
    },
    "Joshua": {
        "start_time": datetime(2024, 7, 26, 16, 30),
        "end_time": datetime(2024, 7, 26, 18, 15),
        "min_duration": 105
    },
    "Brian": {
        "start_time": datetime(2024, 7, 26, 9, 30),
        "end_time": datetime(2024, 7, 26, 15, 30),
        "min_duration": 45
    },
    "Steven": {
        "start_time": datetime(2024, 7, 26, 19, 30),
        "end_time": datetime(2024, 7, 26, 21, 0),
        "min_duration": 90
    },
    "Betty": {
        "start_time": datetime(2024, 7, 26, 19, 0),
        "end_time": datetime(2024, 7, 26, 20, 30),
        "min_duration": 90
    }
}

def compute_travel_time(start_location, end_location):
    return travel_distances[start_location][end_location]

def is_valid_schedule(schedule, constraints):
    for person, constraint in constraints.items():
        start_time = constraint["start_time"]
        end_time = constraint["end_time"]
        min_duration = constraint["min_duration"]
        for meeting in schedule:
            if meeting["person"] == person and start_time <= meeting["start_time"] <= end_time and end_time <= meeting["end_time"]:
                if meeting["end_time"] - meeting["start_time"] < timedelta(minutes=min_duration):
                    return False
    return True

def generate_schedule(constraints):
    start_time = datetime(2024, 7, 26, 9, 0)
    schedule = []
    current_location = "Union Square"
    for person, constraint in constraints.items():
        start_time = constraint["start_time"]
        end_time = constraint["end_time"]
        min_duration = constraint["min_duration"]
        while start_time <= end_time:
            meeting_start_time = start_time
            meeting_end_time = start_time + timedelta(minutes=min_duration)
            travel_time = compute_travel_time(current_location, person)
            meeting_start_time += timedelta(minutes=travel_time)
            schedule.append({"action": "meet", "location": person, "person": person, "start_time": meeting_start_time.strftime("%H:%M"), "end_time": meeting_end_time.strftime("%H:%M")})
            current_location = person
            start_time = meeting_end_time
    return schedule

def optimize_schedule(constraints):
    schedule = generate_schedule(constraints)
    while not is_valid_schedule(schedule, constraints):
        schedule.sort(key=lambda x: x["start_time"])
        current_location = "Union Square"
        for i in range(len(schedule) - 1):
            meeting = schedule[i]
            next_meeting = schedule[i + 1]
            travel_time = compute_travel_time(current_location, meeting["location"])
            if next_meeting["start_time"] - meeting["end_time"] < timedelta(minutes=travel_time):
                schedule.pop(i + 1)
                schedule.insert(i + 1, {"action": "travel", "location": current_location, "person": None, "start_time": meeting["end_time"].strftime("%H:%M"), "end_time": (meeting["end_time"] + timedelta(minutes=travel_time)).strftime("%H:%M")})
                current_location = meeting["location"]
    return schedule

def format_schedule(schedule):
    formatted_schedule = []
    for meeting in schedule:
        if meeting["action"] == "meet":
            formatted_schedule.append({"action": "meet", "location": meeting["location"], "person": meeting["person"], "start_time": meeting["start_time"], "end_time": meeting["end_time"]})
        else:
            formatted_schedule.append({"action": "travel", "location": meeting["location"], "person": None, "start_time": meeting["start_time"], "end_time": meeting["end_time"]})
    return formatted_schedule

def main():
    schedule = optimize_schedule(constraints)
    formatted_schedule = format_schedule(schedule)
    output = {"itinerary": formatted_schedule}
    print(json.dumps(output, indent=4))

if __name__ == "__main__":
    main()