import json
import itertools

# Travel distances in minutes
travel_distances = {
    "Sunset District": {
        "Alamo Square": 17,
        "Russian Hill": 24,
        "Golden Gate Park": 11,
        "Mission District": 24
    },
    "Alamo Square": {
        "Sunset District": 16,
        "Russian Hill": 13,
        "Golden Gate Park": 9,
        "Mission District": 10
    },
    "Russian Hill": {
        "Sunset District": 23,
        "Alamo Square": 15,
        "Golden Gate Park": 21,
        "Mission District": 16
    },
    "Golden Gate Park": {
        "Sunset District": 10,
        "Alamo Square": 10,
        "Russian Hill": 19,
        "Mission District": 17
    },
    "Mission District": {
        "Sunset District": 24,
        "Alamo Square": 11,
        "Russian Hill": 15,
        "Golden Gate Park": 17
    }
}

# Constraints
constraints = {
    "Charles": {"location": "Alamo Square", "start_time": "18:00", "end_time": "20:45", "min_meeting_time": 90},
    "Margaret": {"location": "Russian Hill", "start_time": "09:00", "end_time": "16:00", "min_meeting_time": 30},
    "Daniel": {"location": "Golden Gate Park", "start_time": "08:00", "end_time": "13:30", "min_meeting_time": 15},
    "Stephanie": {"location": "Mission District", "start_time": "20:30", "end_time": "22:00", "min_meeting_time": 90}
}

# Arrival time
arrival_time = "09:00"

def calculate_travel_time(start_location, end_location):
    return travel_distances[start_location][end_location]

def is_valid_meeting(start_time, end_time, meeting_time, location, person):
    return (start_time >= constraints[person]["start_time"] and start_time <= constraints[person]["end_time"]) and \
           (end_time >= constraints[person]["start_time"] and end_time <= constraints[person]["end_time"]) and \
           (end_time - start_time >= constraints[person]["min_meeting_time"])

def generate_itinerary():
    # Generate all possible meeting times
    meeting_times = []
    for person in constraints:
        start_time = constraints[person]["start_time"]
        end_time = constraints[person]["end_time"]
        min_meeting_time = constraints[person]["min_meeting_time"]
        for hour in range(int(start_time[:2]), int(end_time[:2]) + 1):
            for minute in range(0, 60, 15):
                meeting_time = f"{hour:02d}:{minute:02d}"
                meeting_times.append((person, meeting_time, constraints[person]["location"]))

    # Generate all possible meeting locations
    locations = ["Sunset District"]
    for person in constraints:
        locations.append(constraints[person]["location"])

    # Generate all possible meeting combinations
    combinations = list(itertools.product(meeting_times, locations))
    valid_combinations = []

    for combination in combinations:
        meeting_time_info = combination[0]  # unpack the tuple into a variable
        location = combination[1]  # unpack the tuple into a variable
        person, meeting_time, location = meeting_time_info  # unpack the meeting time info into three variables
        start_time = meeting_time
        end_time = meeting_time
        if location == "Sunset District":
            start_time = arrival_time
            end_time = meeting_time
        elif location == "Alamo Square":
            travel_time = calculate_travel_time("Sunset District", "Alamo Square")
            start_time = (int(meeting_time[:2]) - int(arrival_time[:2]) - travel_time // 60) % 24
            if start_time < 10:
                start_time = f"0{start_time:02d}:00"
            else:
                start_time = f"{start_time:02d}:00"
            end_time = meeting_time
        elif location == "Russian Hill":
            travel_time = calculate_travel_time("Sunset District", "Russian Hill")
            start_time = (int(meeting_time[:2]) - int(arrival_time[:2]) - travel_time // 60) % 24
            if start_time < 10:
                start_time = f"0{start_time:02d}:00"
            else:
                start_time = f"{start_time:02d}:00"
            end_time = meeting_time
        elif location == "Golden Gate Park":
            travel_time = calculate_travel_time("Sunset District", "Golden Gate Park")
            start_time = (int(meeting_time[:2]) - int(arrival_time[:2]) - travel_time // 60) % 24
            if start_time < 10:
                start_time = f"0{start_time:02d}:00"
            else:
                start_time = f"{start_time:02d}:00"
            end_time = meeting_time
        elif location == "Mission District":
            travel_time = calculate_travel_time("Sunset District", "Mission District")
            start_time = (int(meeting_time[:2]) - int(arrival_time[:2]) - travel_time // 60) % 24
            if start_time < 10:
                start_time = f"0{start_time:02d}:00"
            else:
                start_time = f"{start_time:02d}:00"
            end_time = meeting_time

        # Check if the meeting is valid
        if is_valid_meeting(start_time, end_time, 15, location, person):
            valid_combinations.append(combination)

    # Find the optimal itinerary
    optimal_itinerary = []
    for combination in valid_combinations:
        meeting_time_info = combination[0]  # unpack the tuple into a variable
        location = combination[1]  # unpack the tuple into a variable
        person, meeting_time, location = meeting_time_info  # unpack the meeting time info into three variables
        start_time = meeting_time
        end_time = meeting_time
        if location == "Sunset District":
            start_time = arrival_time
            end_time = meeting_time
        elif location == "Alamo Square":
            travel_time = calculate_travel_time("Sunset District", "Alamo Square")
            start_time = (int(meeting_time[:2]) - int(arrival_time[:2]) - travel_time // 60) % 24
            if start_time < 10:
                start_time = f"0{start_time:02d}:00"
            else:
                start_time = f"{start_time:02d}:00"
            end_time = meeting_time
        elif location == "Russian Hill":
            travel_time = calculate_travel_time("Sunset District", "Russian Hill")
            start_time = (int(meeting_time[:2]) - int(arrival_time[:2]) - travel_time // 60) % 24
            if start_time < 10:
                start_time = f"0{start_time:02d}:00"
            else:
                start_time = f"{start_time:02d}:00"
            end_time = meeting_time
        elif location == "Golden Gate Park":
            travel_time = calculate_travel_time("Sunset District", "Golden Gate Park")
            start_time = (int(meeting_time[:2]) - int(arrival_time[:2]) - travel_time // 60) % 24
            if start_time < 10:
                start_time = f"0{start_time:02d}:00"
            else:
                start_time = f"{start_time:02d}:00"
            end_time = meeting_time
        elif location == "Mission District":
            travel_time = calculate_travel_time("Sunset District", "Mission District")
            start_time = (int(meeting_time[:2]) - int(arrival_time[:2]) - travel_time // 60) % 24
            if start_time < 10:
                start_time = f"0{start_time:02d}:00"
            else:
                start_time = f"{start_time:02d}:00"
            end_time = meeting_time

        # Add the meeting to the itinerary
        optimal_itinerary.append({"action": "meet", "location": location, "person": person, "start_time": start_time, "end_time": end_time})

    return optimal_itinerary

def main():
    itinerary = generate_itinerary()
    print(json.dumps({"itinerary": itinerary}, indent=4))

if __name__ == "__main__":
    main()