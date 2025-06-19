import json
from datetime import datetime, timedelta

# Travel distances in minutes
travel_distances = {
    "North Beach": {
        "Pacific Heights": 8,
        "Chinatown": 6,
        "Union Square": 7,
        "Mission District": 18,
        "Golden Gate Park": 22,
        "Nob Hill": 7
    },
    "Pacific Heights": {
        "North Beach": 9,
        "Chinatown": 11,
        "Union Square": 12,
        "Mission District": 15,
        "Golden Gate Park": 15,
        "Nob Hill": 8
    },
    "Chinatown": {
        "North Beach": 3,
        "Pacific Heights": 10,
        "Union Square": 7,
        "Mission District": 18,
        "Golden Gate Park": 23,
        "Nob Hill": 8
    },
    "Union Square": {
        "North Beach": 10,
        "Pacific Heights": 15,
        "Chinatown": 7,
        "Mission District": 14,
        "Golden Gate Park": 22,
        "Nob Hill": 9
    },
    "Mission District": {
        "North Beach": 17,
        "Pacific Heights": 16,
        "Chinatown": 16,
        "Union Square": 15,
        "Golden Gate Park": 17,
        "Nob Hill": 12
    },
    "Golden Gate Park": {
        "North Beach": 24,
        "Pacific Heights": 16,
        "Chinatown": 23,
        "Union Square": 22,
        "Mission District": 17,
        "Nob Hill": 20
    },
    "Nob Hill": {
        "North Beach": 8,
        "Pacific Heights": 8,
        "Chinatown": 6,
        "Union Square": 7,
        "Mission District": 13,
        "Golden Gate Park": 17
    }
}

# Meeting constraints
constraints = [
    {"location": "Pacific Heights", "start_time": "20:00", "end_time": "22:00", "min_meeting_time": 120},
    {"location": "Chinatown", "start_time": "12:15", "end_time": "16:45", "min_meeting_time": 90},
    {"location": "Union Square", "start_time": "09:30", "end_time": "15:30", "min_meeting_time": 120},
    {"location": "Mission District", "start_time": "18:15", "end_time": "21:15", "min_meeting_time": 15},
    {"location": "Golden Gate Park", "start_time": "11:30", "end_time": "17:45", "min_meeting_time": 15},
    {"location": "Nob Hill", "start_time": "08:00", "end_time": "15:30", "min_meeting_time": 15}
]

def calculate_arrival_time(departure_time, travel_time):
    departure_time = datetime.strptime(departure_time, "%H:%M")
    arrival_time = departure_time + timedelta(minutes=travel_time)
    return arrival_time.strftime("%H:%M")

def compute_meeting_schedule():
    schedule = []
    current_time = "09:00"
    current_location = "North Beach"

    for constraint in constraints:
        if current_time < constraint["start_time"]:
            schedule.append({"action": "travel", "location": current_location, "destination": constraint["location"], "start_time": current_time, "end_time": calculate_arrival_time(current_time, travel_distances[current_location][constraint["location"]])})
            current_location = constraint["location"]
            current_time = calculate_arrival_time(current_time, travel_distances[current_location][constraint["location"]])

        schedule.append({"action": "meet", "location": current_location, "person": constraint["location"], "start_time": current_time, "end_time": calculate_arrival_time(current_time, constraint["min_meeting_time"])})

        if current_time < constraint["end_time"]:
            schedule.append({"action": "travel", "location": current_location, "destination": "North Beach", "start_time": current_time, "end_time": calculate_arrival_time(current_time, travel_distances[current_location]["North Beach"])})
            current_location = "North Beach"
            current_time = calculate_arrival_time(current_time, travel_distances[current_location]["North Beach"])

    return schedule

def main():
    schedule = compute_meeting_schedule()
    print(json.dumps({"itinerary": schedule}, indent=4))

if __name__ == "__main__":
    main()