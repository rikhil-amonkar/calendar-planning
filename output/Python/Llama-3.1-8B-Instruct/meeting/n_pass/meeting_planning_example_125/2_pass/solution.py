import json
from datetime import datetime, timedelta

# Input parameters
travel_distances = {
    "Embarcadero to Financial District": 5,
    "Embarcadero to Alamo Square": 19,
    "Financial District to Embarcadero": 4,
    "Financial District to Alamo Square": 17,
    "Alamo Square to Embarcadero": 17,
    "Alamo Square to Financial District": 17
}

constraints = {
    "Stephanie": {"start_time": "08:15", "end_time": "11:30", "min_meeting_time": 90},
    "John": {"start_time": "10:15", "end_time": "20:45", "min_meeting_time": 30}
}

def calculate_travel_time(location1, location2, travel_distances):
    travel_time = travel_distances[f"{location1} to {location2}"]
    return travel_time

def compute_schedule():
    # Start at Embarcadero at 9:00 AM
    current_location = "Embarcadero"
    current_time = datetime.strptime("09:00", "%H:%M")

    schedule = []

    # Meet Stephanie
    stephanie_start_time = datetime.strptime(constraints["Stephanie"]["start_time"], "%H:%M")
    stephanie_end_time = datetime.strptime(constraints["Stephanie"]["end_time"], "%H:%M")

    # Check if we can meet Stephanie
    if stephanie_start_time < current_time and current_time + timedelta(minutes=calculate_travel_time(current_location, "Financial District", travel_distances)) + timedelta(minutes=constraints["Stephanie"]["min_meeting_time"]) <= stephanie_end_time:
        schedule.append({"action": "meet", "location": "Financial District", "person": "Stephanie", "start_time": current_time.strftime("%H:%M"), "end_time": (current_time + timedelta(minutes=constraints["Stephanie"]["min_meeting_time"] + calculate_travel_time("Financial District", current_location, travel_distances))).strftime("%H:%M")})

        # Update current time and location
        current_time = current_time + timedelta(minutes=constraints["Stephanie"]["min_meeting_time"] + calculate_travel_time("Financial District", current_location, travel_distances))
        current_location = "Financial District"

    # Meet John
    john_start_time = datetime.strptime(constraints["John"]["start_time"], "%H:%M")
    john_end_time = datetime.strptime(constraints["John"]["end_time"], "%H:%M")

    # Check if we can meet John
    if john_start_time < current_time and current_time + timedelta(minutes=calculate_travel_time(current_location, "Alamo Square", travel_distances)) + timedelta(minutes=constraints["John"]["min_meeting_time"]) <= john_end_time:
        schedule.append({"action": "meet", "location": "Alamo Square", "person": "John", "start_time": current_time.strftime("%H:%M"), "end_time": (current_time + timedelta(minutes=constraints["John"]["min_meeting_time"] + calculate_travel_time("Alamo Square", current_location, travel_distances))).strftime("%H:%M")})

        # Update current time and location
        current_time = current_time + timedelta(minutes=constraints["John"]["min_meeting_time"] + calculate_travel_time("Alamo Square", current_location, travel_distances))
        current_location = "Alamo Square"

    return schedule

def main():
    schedule = compute_schedule()
    print(json.dumps({"itinerary": schedule}, indent=4))

if __name__ == "__main__":
    main()