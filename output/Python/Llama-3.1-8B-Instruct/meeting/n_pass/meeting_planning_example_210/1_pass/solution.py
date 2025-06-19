import json
from datetime import datetime, timedelta

# Define travel distances in minutes
travel_distances = {
    "Fisherman's Wharf to Presidio": 17,
    "Fisherman's Wharf to Richmond District": 18,
    "Fisherman's Wharf to Financial District": 11,
    "Presidio to Fisherman's Wharf": 19,
    "Presidio to Richmond District": 7,
    "Presidio to Financial District": 23,
    "Richmond District to Fisherman's Wharf": 18,
    "Richmond District to Presidio": 7,
    "Richmond District to Financial District": 22,
    "Financial District to Fisherman's Wharf": 10,
    "Financial District to Presidio": 22,
    "Financial District to Richmond District": 21
}

# Define constraints
constraints = {
    "Emily": {"start_time": datetime(2024, 7, 26, 16, 15), "end_time": datetime(2024, 7, 26, 21, 0), "min_meeting_time": 105},
    "Joseph": {"start_time": datetime(2024, 7, 26, 17, 15), "end_time": datetime(2024, 7, 26, 22, 0), "min_meeting_time": 120},
    "Melissa": {"start_time": datetime(2024, 7, 26, 15, 45), "end_time": datetime(2024, 7, 26, 21, 45), "min_meeting_time": 75}
}

# Define start time
start_time = datetime(2024, 7, 26, 9, 0)

def calculate_travel_time(location1, location2):
    return travel_distances[f"{location1} to {location2}"]

def is_valid_meeting(person, start_time, end_time):
    return start_time >= constraints[person]["start_time"] and end_time <= constraints[person]["end_time"]

def calculate_meeting_time(person, start_time, end_time):
    return (end_time - start_time).total_seconds() / 60

def find_optimal_meeting_schedule():
    itinerary = []
    current_time = start_time
    locations = ["Fisherman's Wharf", "Presidio", "Richmond District", "Financial District"]

    # Visit each location
    for location in locations:
        # Visit each person at the current location
        for person in constraints:
            if location == "Fisherman's Wharf" and person == "Emily":
                continue
            if location == "Presidio" and person == "Joseph":
                continue
            if location == "Financial District" and person == "Melissa":
                continue

            # Check if the person is available at the current location
            if is_valid_meeting(person, current_time, current_time + timedelta(minutes=calculate_travel_time(location, "Fisherman's Wharf"))):
                # Calculate the end time of the meeting
                end_time = current_time + timedelta(minutes=calculate_meeting_time(person, current_time, current_time + timedelta(minutes=calculate_travel_time(location, "Fisherman's Wharf"))))

                # Check if the meeting time is sufficient
                if calculate_meeting_time(person, current_time, end_time) >= constraints[person]["min_meeting_time"]:
                    itinerary.append({
                        "action": "meet",
                        "location": location,
                        "person": person,
                        "start_time": current_time.strftime("%H:%M"),
                        "end_time": end_time.strftime("%H:%M")
                    })

                    # Update the current time
                    current_time = end_time + timedelta(minutes=calculate_travel_time(location, "Fisherman's Wharf"))

    return itinerary

def main():
    itinerary = find_optimal_meeting_schedule()
    print(json.dumps({"itinerary": itinerary}, indent=4))

if __name__ == "__main__":
    main()