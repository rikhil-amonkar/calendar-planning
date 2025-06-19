import json
from datetime import datetime, timedelta

# Travel distances (in minutes)
travel_distances = {
    "Marina District": {
        "Bayview": 27,
        "Sunset District": 19,
        "Richmond District": 11,
        "Nob Hill": 12,
        "Chinatown": 15,
        "Haight-Ashbury": 16,
        "North Beach": 11,
        "Russian Hill": 8,
        "Embarcadero": 14
    },
    "Bayview": {
        "Marina District": 27,
        "Sunset District": 23,
        "Richmond District": 25,
        "Nob Hill": 20,
        "Chinatown": 19,
        "Haight-Ashbury": 19,
        "North Beach": 22,
        "Russian Hill": 23,
        "Embarcadero": 19
    },
    "Sunset District": {
        "Marina District": 19,
        "Bayview": 22,
        "Richmond District": 12,
        "Nob Hill": 27,
        "Chinatown": 30,
        "Haight-Ashbury": 15,
        "North Beach": 28,
        "Russian Hill": 24,
        "Embarcadero": 30
    },
    "Richmond District": {
        "Marina District": 11,
        "Bayview": 27,
        "Sunset District": 11,
        "Nob Hill": 17,
        "Chinatown": 20,
        "Haight-Ashbury": 10,
        "North Beach": 17,
        "Russian Hill": 13,
        "Embarcadero": 19
    },
    "Nob Hill": {
        "Marina District": 12,
        "Bayview": 19,
        "Sunset District": 24,
        "Richmond District": 14,
        "Chinatown": 6,
        "Haight-Ashbury": 13,
        "North Beach": 8,
        "Russian Hill": 5,
        "Embarcadero": 9
    },
    "Chinatown": {
        "Marina District": 15,
        "Bayview": 20,
        "Sunset District": 29,
        "Richmond District": 20,
        "Nob Hill": 9,
        "Haight-Ashbury": 19,
        "North Beach": 3,
        "Russian Hill": 7,
        "Embarcadero": 5
    },
    "Haight-Ashbury": {
        "Marina District": 16,
        "Bayview": 18,
        "Sunset District": 15,
        "Richmond District": 10,
        "Nob Hill": 15,
        "Chinatown": 19,
        "North Beach": 19,
        "Russian Hill": 17,
        "Embarcadero": 20
    },
    "North Beach": {
        "Marina District": 11,
        "Bayview": 25,
        "Sunset District": 27,
        "Richmond District": 18,
        "Nob Hill": 7,
        "Chinatown": 6,
        "Haight-Ashbury": 18,
        "Russian Hill": 4,
        "Embarcadero": 6
    },
    "Russian Hill": {
        "Marina District": 8,
        "Bayview": 23,
        "Sunset District": 23,
        "Richmond District": 14,
        "Nob Hill": 5,
        "Chinatown": 9,
        "Haight-Ashbury": 17,
        "North Beach": 5,
        "Embarcadero": 8
    },
    "Embarcadero": {
        "Marina District": 14,
        "Bayview": 19,
        "Sunset District": 30,
        "Richmond District": 21,
        "Nob Hill": 10,
        "Chinatown": 7,
        "Haight-Ashbury": 21,
        "North Beach": 5,
        "Russian Hill": 8
    }
}

# Meeting constraints
constraints = {
    "Charles": {"start": 1130, "end": 1430, "min_time": 45},
    "Robert": {"start": 1745, "end": 2100, "min_time": 30},
    "Karen": {"start": 1915, "end": 2130, "min_time": 60},
    "Rebecca": {"start": 1715, "end": 2030, "min_time": 90},
    "Margaret": {"start": 1315, "end": 1945, "min_time": 120},
    "Patricia": {"start": 1430, "end": 2030, "min_time": 45},
    "Mark": {"start": 1400, "end": 1830, "min_time": 105},
    "Melissa": {"start": 1300, "end": 1945, "min_time": 30},
    "Laura": {"start": 745, "end": 1215, "min_time": 105}
}

def calculate_travel_time(start_location, end_location):
    return travel_distances[start_location][end_location]

def is_valid_meeting(start_time, end_time, start_location, end_location):
    travel_time = calculate_travel_time(start_location, end_location)
    return end_time - start_time >= travel_time + constraints[end_location]["min_time"]

def find_meeting_times(start_time, end_time, start_location, end_location):
    meeting_times = []
    for hour in range(start_time, end_time):
        for minute in range(0, 60, 15):
            meeting_time = datetime.strptime(f"{hour:02d}{minute:02d}", "%H%M")
            if is_valid_meeting(start_time, end_time, start_location, end_location):
                meeting_times.append(meeting_time.strftime("%H:%M"))
    return meeting_times

def find_optimal_meeting_schedule():
    optimal_schedule = []
    start_time = 900
    end_time = 2100

    # Find optimal meeting times for each person
    for person, constraint in constraints.items():
        start_location = "Marina District"
        end_location = datetime.strptime(constraint["start"], "%H%M").time()
        meeting_times = find_meeting_times(start_time, end_time, start_location, end_location)
        optimal_schedule.append({"action": "meet", "location": end_location, "person": person, "start_time": meeting_times[0], "end_time": meeting_times[0]})

    # Add travel times between meetings
    for i in range(len(optimal_schedule) - 1):
        start_location = optimal_schedule[i]["location"]
        end_location = datetime.strptime(optimal_schedule[i+1]["start_time"], "%H:%M").time()
        travel_time = calculate_travel_time(start_location.strftime("%H%M"), end_location.strftime("%H%M"))
        optimal_schedule[i]["end_time"] = datetime.strptime(optimal_schedule[i]["end_time"], "%H:%M") + timedelta(minutes=travel_time)
        optimal_schedule[i+1]["start_time"] = datetime.strptime(optimal_schedule[i+1]["start_time"], "%H:%M") - timedelta(minutes=travel_time)

    return optimal_schedule

def main():
    optimal_schedule = find_optimal_meeting_schedule()
    itinerary = [{"action": "meet", "location": item["location"].strftime("%H:%M"), "person": item["person"], "start_time": item["start_time"], "end_time": item["end_time"]} for item in optimal_schedule]
    print(json.dumps({"itinerary": itinerary}, indent=4))

if __name__ == "__main__":
    main()