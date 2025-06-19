import json
import datetime

# Travel distances in minutes
travel_distances = {
    "Financial District": {
        "Russian Hill": 10,
        "Sunset District": 31,
        "North Beach": 7,
        "The Castro": 23,
        "Golden Gate Park": 23
    },
    "Russian Hill": {
        "Financial District": 11,
        "Sunset District": 23,
        "North Beach": 5,
        "The Castro": 21,
        "Golden Gate Park": 21
    },
    "Sunset District": {
        "Financial District": 30,
        "Russian Hill": 24,
        "North Beach": 29,
        "The Castro": 17,
        "Golden Gate Park": 11
    },
    "North Beach": {
        "Financial District": 8,
        "Russian Hill": 4,
        "Sunset District": 27,
        "The Castro": 22,
        "Golden Gate Park": 22
    },
    "The Castro": {
        "Financial District": 20,
        "Russian Hill": 18,
        "Sunset District": 17,
        "North Beach": 20,
        "Golden Gate Park": 13
    },
    "Golden Gate Park": {
        "Financial District": 26,
        "Russian Hill": 19,
        "Sunset District": 10,
        "North Beach": 24,
        "The Castro": 13
    }
}

# Meeting constraints
constraints = [
    {"name": "Ronald", "location": "Russian Hill", "start_time": "13:45", "end_time": "17:15", "min_time": 105},
    {"name": "Patricia", "location": "Sunset District", "start_time": "09:15", "end_time": "22:00", "min_time": 60},
    {"name": "Laura", "location": "North Beach", "start_time": "12:30", "end_time": "12:45", "min_time": 15},
    {"name": "Emily", "location": "The Castro", "start_time": "16:15", "end_time": "18:30", "min_time": 60},
    {"name": "Mary", "location": "Golden Gate Park", "start_time": "15:00", "end_time": "16:30", "min_time": 60}
]

# Function to calculate travel time
def calculate_travel_time(start_location, end_location):
    return travel_distances[start_location][end_location]

# Function to check if meeting is possible
def is_meeting_possible(start_time, end_time, min_time, location, person):
    for constraint in constraints:
        if constraint["name"] == person:
            if start_time >= constraint["start_time"] and start_time <= constraint["end_time"]:
                travel_time_to_location = calculate_travel_time("Financial District", location)
                travel_time_from_location = calculate_travel_time(location, "Financial District")
                return end_time - start_time >= min_time + travel_time_to_location + travel_time_from_location
    return False

# Function to generate itinerary
def generate_itinerary():
    itinerary = []
    current_time = datetime.datetime.strptime("09:00", "%H:%M")
    for constraint in constraints:
        person = constraint["name"]
        location = constraint["location"]
        start_time = datetime.datetime.strptime(constraint["start_time"], "%H:%M")
        end_time = datetime.datetime.strptime(constraint["end_time"], "%H:%M")
        min_time = constraint["min_time"]
        if is_meeting_possible(current_time.strftime("%H:%M"), end_time.strftime("%H:%M"), min_time, location, person):
            travel_time_to_location = calculate_travel_time("Financial District", location)
            travel_time_from_location = calculate_travel_time(location, "Financial District")
            total_travel_time = travel_time_to_location + travel_time_from_location
            end_time = current_time + datetime.timedelta(minutes=min_time + total_travel_time)
            itinerary.append({
                "action": "meet",
                "location": location,
                "person": person,
                "start_time": current_time.strftime("%H:%M"),
                "end_time": end_time.strftime("%H:%M")
            })
            current_time = end_time
    return itinerary

# Generate itinerary and print as JSON
itinerary = generate_itinerary()
print(json.dumps({"itinerary": itinerary}, indent=4))