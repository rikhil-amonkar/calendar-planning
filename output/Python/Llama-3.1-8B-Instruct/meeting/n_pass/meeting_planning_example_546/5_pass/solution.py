import json
from datetime import datetime, timedelta

# Define travel distances in minutes
travel_distances = {
    "Embarcadero": {
        "Richmond District": 21,
        "Union Square": 10,
        "Financial District": 5,
        "Pacific Heights": 11,
        "Nob Hill": 10,
        "Bayview": 21
    },
    "Richmond District": {
        "Embarcadero": 19,
        "Union Square": 21,
        "Financial District": 22,
        "Pacific Heights": 10,
        "Nob Hill": 17,
        "Bayview": 26
    },
    "Union Square": {
        "Embarcadero": 11,
        "Richmond District": 20,
        "Financial District": 9,
        "Pacific Heights": 15,
        "Nob Hill": 9,
        "Bayview": 15
    },
    "Financial District": {
        "Embarcadero": 4,
        "Richmond District": 21,
        "Union Square": 9,
        "Pacific Heights": 13,
        "Nob Hill": 8,
        "Bayview": 19
    },
    "Pacific Heights": {
        "Embarcadero": 10,
        "Richmond District": 12,
        "Union Square": 12,
        "Financial District": 13,
        "Nob Hill": 8,
        "Bayview": 22
    },
    "Nob Hill": {
        "Embarcadero": 9,
        "Richmond District": 14,
        "Union Square": 7,
        "Financial District": 9,
        "Pacific Heights": 8,
        "Bayview": 19
    },
    "Bayview": {
        "Embarcadero": 19,
        "Richmond District": 25,
        "Union Square": 17,
        "Financial District": 19,
        "Pacific Heights": 23,
        "Nob Hill": 20
    }
}

# Define meeting constraints
meeting_constraints = {
    "Kenneth": {"location": "Richmond District", "start_time": "21:15", "end_time": "22:00"},
    "Lisa": {"location": "Union Square", "start_time": "09:00", "end_time": "16:30"},
    "Joshua": {"location": "Financial District", "start_time": "12:00", "end_time": "15:15"},
    "Nancy": {"location": "Pacific Heights", "start_time": "08:00", "end_time": "11:30"},
    "Andrew": {"location": "Nob Hill", "start_time": "11:30", "end_time": "20:15"},
    "John": {"location": "Bayview", "start_time": "16:45", "end_time": "21:30"}
}

def calculate_travel_time(start_location, end_location):
    return travel_distances[start_location][end_location]

def is_meeting_possible(meeting, start_time):
    location = meeting["location"]
    start_time_meeting = datetime.strptime(meeting["start_time"], "%H:%M")
    end_time_meeting = datetime.strptime(meeting["end_time"], "%H:%M")
    travel_time = calculate_travel_time("Embarcadero", location)
    return (start_time + timedelta(minutes=travel_time)) <= start_time_meeting

def calculate_meeting_duration(meeting):
    start_time_meeting = datetime.strptime(meeting["start_time"], "%H:%M")
    end_time_meeting = datetime.strptime(meeting["end_time"], "%H:%M")
    return (end_time_meeting - start_time_meeting).total_seconds() / 60

def compute_meeting_schedule():
    schedule = []
    start_time = datetime.strptime("09:00", "%H:%M")
    locations = ["Pacific Heights", "Union Square", "Financial District", "Nob Hill", "Bayview"]
    for location in locations:
        for person in meeting_constraints:
            meeting = meeting_constraints[person]
            if meeting["location"] == location and is_meeting_possible(meeting, start_time):
                travel_time = calculate_travel_time("Embarcadero", location)
                end_time = start_time + timedelta(minutes=travel_time)
                if person == "Nancy":
                    end_time += timedelta(minutes=calculate_meeting_duration(meeting) + 30)
                elif person == "Lisa":
                    end_time += timedelta(minutes=calculate_meeting_duration(meeting) + 30)
                elif person == "Joshua":
                    meeting_duration = calculate_meeting_duration(meeting)
                    # Check if the start time of the meeting is within Joshua's availability
                    if datetime.strptime(meeting["start_time"], "%H:%M") >= datetime.strptime("12:00", "%H:%M") and datetime.strptime(meeting["start_time"], "%H:%M") <= datetime.strptime(meeting["end_time"], "%H:%M"):
                        end_time += timedelta(minutes=meeting_duration + 15)
                elif person == "Kenneth":
                    end_time += timedelta(minutes=calculate_meeting_duration(meeting))
                elif person == "Andrew":
                    end_time += timedelta(minutes=calculate_meeting_duration(meeting) + 30)
                elif person == "John":
                    end_time += timedelta(minutes=calculate_meeting_duration(meeting) + 30)
                schedule.append({"action": "meet", "location": meeting["location"], "person": person, "start_time": start_time.strftime("%H:%M"), "end_time": end_time.strftime("%H:%M")})
                start_time = end_time
                break
    return schedule

def main():
    schedule = compute_meeting_schedule()
    print(json.dumps({"itinerary": schedule}, indent=4))

if __name__ == "__main__":
    main()