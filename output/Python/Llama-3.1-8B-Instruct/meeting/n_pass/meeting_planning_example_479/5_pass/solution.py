import json
from datetime import datetime, timedelta

# Define travel distances in minutes
travel_distances = {
    "Embarcadero": {
        "Golden Gate Park": 25,
        "Haight-Ashbury": 21,
        "Bayview": 21,
        "Presidio": 20,
        "Financial District": 5
    },
    "Golden Gate Park": {
        "Embarcadero": 25,
        "Haight-Ashbury": 7,
        "Bayview": 23,
        "Presidio": 11,
        "Financial District": 26
    },
    "Haight-Ashbury": {
        "Embarcadero": 20,
        "Golden Gate Park": 7,
        "Bayview": 18,
        "Presidio": 15,
        "Financial District": 21
    },
    "Bayview": {
        "Embarcadero": 19,
        "Golden Gate Park": 22,
        "Haight-Ashbury": 19,
        "Presidio": 31,
        "Financial District": 19
    },
    "Presidio": {
        "Embarcadero": 20,
        "Golden Gate Park": 12,
        "Haight-Ashbury": 15,
        "Bayview": 31,
        "Financial District": 23
    },
    "Financial District": {
        "Embarcadero": 4,
        "Golden Gate Park": 23,
        "Haight-Ashbury": 19,
        "Bayview": 19,
        "Presidio": 22
    }
}

# Define meeting constraints
constraints = {
    "Mary": {
        "start_time": datetime(2024, 7, 26, 8, 45),
        "end_time": datetime(2024, 7, 26, 11, 45),
        "meeting_duration": 45
    },
    "Kevin": {
        "start_time": datetime(2024, 7, 26, 10, 15),
        "end_time": datetime(2024, 7, 26, 16, 15),
        "meeting_duration": 90
    },
    "Deborah": {
        "start_time": datetime(2024, 7, 26, 15, 0),
        "end_time": datetime(2024, 7, 26, 19, 15),
        "meeting_duration": 120
    },
    "Stephanie": {
        "start_time": datetime(2024, 7, 26, 10, 0),
        "end_time": datetime(2024, 7, 26, 17, 15),
        "meeting_duration": 120
    },
    "Emily": {
        "start_time": datetime(2024, 7, 26, 11, 30),
        "end_time": datetime(2024, 7, 26, 21, 45),
        "meeting_duration": 105
    }
}

def compute_itinerary():
    # Initialize itinerary
    itinerary = []

    # Start at Embarcadero at 9:00 AM
    current_location = "Embarcadero"
    current_time = datetime(2024, 7, 26, 9, 0)

    # Define locations to visit
    locations_to_visit = ["Golden Gate Park", "Haight-Ashbury", "Bayview", "Presidio", "Financial District"]

    for location in locations_to_visit:
        # Travel to the next location
        if current_location!= location:
            travel_time = 0
            for current_location_name in [current_location, location]:
                if current_location_name in travel_distances and location in travel_distances[current_location_name]:
                    travel_time += travel_distances[current_location_name][location]
                elif current_location_name in travel_distances and location in travel_distances:
                    travel_time += travel_distances[location][current_location_name]
            current_time += timedelta(minutes=travel_time)
            current_location = location

        # Meet people at the current location
        for person, constraint in constraints.items():
            if constraint["start_time"] <= current_time and current_time + timedelta(minutes=constraint["meeting_duration"]) <= constraint["end_time"]:
                itinerary.append({
                    "action": "meet",
                    "location": current_location,
                    "person": person,
                    "start_time": current_time.strftime("%H:%M"),
                    "end_time": (current_time + timedelta(minutes=constraint["meeting_duration"])).strftime("%H:%M")
                })
                current_time += timedelta(minutes=constraint["meeting_duration"])

    return itinerary

def main():
    itinerary = compute_itinerary()
    print(json.dumps({"itinerary": itinerary}, indent=4))

if __name__ == "__main__":
    main()