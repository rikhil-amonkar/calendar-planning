import json
from datetime import datetime, timedelta

# Define travel distances in minutes
travel_distances = {
    "Union Square": {
        "Nob Hill": 9,
        "Haight-Ashbury": 18,
        "Chinatown": 7,
        "Marina District": 18
    },
    "Nob Hill": {
        "Union Square": 7,
        "Haight-Ashbury": 13,
        "Chinatown": 6,
        "Marina District": 11
    },
    "Haight-Ashbury": {
        "Union Square": 17,
        "Nob Hill": 15,
        "Chinatown": 19,
        "Marina District": 17
    },
    "Chinatown": {
        "Union Square": 7,
        "Nob Hill": 8,
        "Haight-Ashbury": 19,
        "Marina District": 12
    },
    "Marina District": {
        "Union Square": 16,
        "Nob Hill": 12,
        "Haight-Ashbury": 16,
        "Chinatown": 16
    }
}

# Define meeting constraints
meeting_constraints = {
    "Karen": {"location": "Nob Hill", "start_time": "21:15", "end_time": "21:45", "min_duration": 30},
    "Joseph": {"location": "Haight-Ashbury", "start_time": "12:30", "end_time": "19:45", "min_duration": 90},
    "Sandra": {"location": "Chinatown", "start_time": "07:15", "end_time": "19:15", "min_duration": 75},
    "Nancy": {"location": "Marina District", "start_time": "11:00", "end_time": "20:15", "min_duration": 105}
}

def calculate_travel_time(current_location, destination):
    """Calculate the travel time between two locations."""
    return travel_distances.get(current_location, {}).get(destination, 0)

def calculate_meeting_start_time(current_location, destination, current_time, meeting_end_time):
    """Calculate the meeting start time based on the current location, destination, current time, and meeting end time."""
    travel_time = calculate_travel_time(current_location, destination)
    if travel_time == 0:
        return current_time
    return (datetime.strptime(current_time, "%H:%M") + timedelta(minutes=travel_time)).strftime("%H:%M")

def is_meeting_possible(current_location, destination, meeting_start_time, meeting_end_time, min_duration):
    """Check if a meeting is possible based on the current location, destination, meeting start time, meeting end time, and minimum duration."""
    travel_time = calculate_travel_time(current_location, destination)
    if travel_time == 0:
        return False
    meeting_duration = (datetime.strptime(meeting_end_time, "%H:%M") - datetime.strptime(meeting_start_time, "%H:%M")).total_seconds() / 60
    return meeting_duration >= min_duration and datetime.strptime(meeting_start_time, "%H:%M") + timedelta(minutes=travel_time) <= datetime.strptime(meeting_end_time, "%H:%M")

def is_person_available(person, meeting_start_time, meeting_end_time):
    """Check if a person is available during the meeting time."""
    constraint = meeting_constraints.get(person)
    if constraint:
        start_time = datetime.strptime(constraint["start_time"], "%H:%M")
        end_time = datetime.strptime(constraint["end_time"], "%H:%M")
        return start_time <= datetime.strptime(meeting_start_time, "%H:%M") < end_time
    return False

def find_optimal_meeting_schedule(current_location, current_time, meeting_constraints):
    """Find the optimal meeting schedule based on the current location, current time, and meeting constraints."""
    optimal_schedule = []
    for person, constraint in meeting_constraints.items():
        destination = constraint["location"]
        meeting_start_time = calculate_meeting_start_time(current_location, destination, current_time, constraint["start_time"])
        if is_meeting_possible(current_location, destination, meeting_start_time, constraint["end_time"], constraint["min_duration"]) and is_person_available(person, meeting_start_time, constraint["end_time"]):
            optimal_schedule.append({
                "action": "meet",
                "location": destination,
                "person": person,
                "start_time": meeting_start_time,
                "end_time": constraint["end_time"]
            })
            current_location = destination
            current_time = constraint["start_time"]
    return optimal_schedule

def main():
    current_location = "Union Square"
    current_time = "09:00"
    optimal_schedule = find_optimal_meeting_schedule(current_location, current_time, meeting_constraints)
    print(json.dumps({"itinerary": optimal_schedule}, indent=4))

if __name__ == "__main__":
    main()