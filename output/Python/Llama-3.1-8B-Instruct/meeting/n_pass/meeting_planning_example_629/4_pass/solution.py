import json
from datetime import datetime, timedelta

# Define travel distances in minutes
travel_distances = {
    "Russian Hill": {
        "Presidio": 14,
        "Chinatown": 9,
        "Pacific Heights": 7,
        "Richmond District": 14,
        "Fisherman's Wharf": 7,
        "Golden Gate Park": 21,
        "Bayview": 23
    },
    "Presidio": {
        "Russian Hill": 14,
        "Chinatown": 21,
        "Pacific Heights": 11,
        "Richmond District": 7,
        "Fisherman's Wharf": 19,
        "Golden Gate Park": 12,
        "Bayview": 31
    },
    "Chinatown": {
        "Russian Hill": 9,
        "Presidio": 19,
        "Pacific Heights": 10,
        "Richmond District": 20,
        "Fisherman's Wharf": 8,
        "Golden Gate Park": 23,
        "Bayview": 22
    },
    "Pacific Heights": {
        "Russian Hill": 7,
        "Presidio": 11,
        "Chinatown": 11,
        "Richmond District": 10,
        "Fisherman's Wharf": 13,
        "Golden Gate Park": 15,
        "Bayview": 22
    },
    "Richmond District": {
        "Russian Hill": 14,
        "Presidio": 7,
        "Chinatown": 20,
        "Pacific Heights": 10,
        "Fisherman's Wharf": 18,
        "Golden Gate Park": 9,
        "Bayview": 26
    },
    "Fisherman's Wharf": {
        "Russian Hill": 7,
        "Presidio": 17,
        "Chinatown": 12,
        "Pacific Heights": 12,
        "Richmond District": 18,
        "Golden Gate Park": 25,
        "Bayview": 26
    },
    "Golden Gate Park": {
        "Russian Hill": 21,
        "Presidio": 11,
        "Chinatown": 23,
        "Pacific Heights": 16,
        "Richmond District": 7,
        "Fisherman's Wharf": 24,
        "Bayview": 23
    },
    "Bayview": {
        "Russian Hill": 23,
        "Presidio": 31,
        "Chinatown": 18,
        "Pacific Heights": 23,
        "Richmond District": 25,
        "Fisherman's Wharf": 25,
        "Golden Gate Park": 22
    }
}

# Define meeting constraints
constraints = {
    "Matthew": {"location": "Presidio", "start_time": 11, "end_time": 21, "duration": 90},
    "Margaret": {"location": "Chinatown", "start_time": 9, "end_time": 18, "duration": 90},
    "Nancy": {"location": "Pacific Heights", "start_time": 14, "end_time": 17, "duration": 15},
    "Helen": {"location": "Richmond District", "start_time": 19, "end_time": 22, "duration": 60},
    "Rebecca": {"location": "Fisherman's Wharf", "start_time": 22, "end_time": 23, "duration": 60},
    "Kimberly": {"location": "Golden Gate Park", "start_time": 13, "end_time": 17, "duration": 120},
    "Kenneth": {"location": "Bayview", "start_time": 14, "end_time": 20, "duration": 60}
}

# Define starting location and time
start_location = "Russian Hill"
start_time = datetime(2024, 1, 1, 9)

# Initialize itinerary
itinerary = []

# Function to calculate end time
def calculate_end_time(start_time, duration):
    return start_time + timedelta(minutes=duration)

# Function to calculate travel time
def calculate_travel_time(location1, location2):
    if location1 in travel_distances and location2 in travel_distances[location1]:
        return travel_distances[location1][location2]
    else:
        return float('inf')  # Return infinity if travel time is not available

# Function to check if meeting is possible
def is_meeting_possible(person, location, start_time):
    end_time = calculate_end_time(start_time, constraints[person]["duration"])
    return constraints[person]["start_time"] <= start_time.time().hour <= constraints[person]["end_time"] and start_time.time().hour + constraints[person]["duration"] / 60 <= constraints[person]["end_time"]

# Function to add meeting to itinerary
def add_meeting(person, location, start_time, end_time):
    itinerary.append({"action": "meet", "location": location, "person": person, "start_time": start_time.strftime("%H:%M"), "end_time": end_time.strftime("%H:%M")})

# Main function to generate itinerary
def generate_itinerary():
    global start_location
    global start_time
    end_time = datetime(2024, 1, 1, 23, 59)
    current_time = start_time
    while current_time <= end_time:
        for person in constraints:
            if person not in itinerary and is_meeting_possible(person, constraints[person]["location"], current_time):
                travel_time = calculate_travel_time(start_location, constraints[person]["location"])
                if travel_time <= (end_time - current_time).total_seconds() / 60:
                    start_time = current_time + timedelta(minutes=travel_time)
                    add_meeting(person, constraints[person]["location"], start_time, calculate_end_time(start_time, constraints[person]["duration"]))
                    start_location = constraints[person]["location"]
                    # Check if Margaret's meeting is possible
                    if person == "Margaret":
                        travel_time = calculate_travel_time(constraints[person]["location"], "Russian Hill")
                        if travel_time <= (end_time - start_time).total_seconds() / 60:
                            next_start_time = start_time + timedelta(minutes=travel_time)
                            if next_start_time.time().hour >= 9 and next_start_time.time().hour <= 18:
                                add_meeting(person, "Russian Hill", next_start_time, calculate_end_time(next_start_time, constraints[person]["duration"]))
                            else:
                                # If Margaret's meeting is not possible, remove it from the itinerary
                                itinerary.pop()
        current_time += timedelta(minutes=1)

# Generate itinerary
generate_itinerary()

# Print itinerary as JSON
print(json.dumps({"itinerary": itinerary}, indent=4))