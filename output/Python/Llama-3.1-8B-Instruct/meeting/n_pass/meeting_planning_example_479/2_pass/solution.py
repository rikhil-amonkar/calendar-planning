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

    # Meet Mary
    if current_time < constraints["Mary"]["start_time"] + timedelta(minutes=constraints["Mary"]["meeting_duration"]):
        itinerary.append({
            "action": "meet",
            "location": "Golden Gate Park",
            "person": "Mary",
            "start_time": constraints["Mary"]["start_time"].strftime("%H:%M"),
            "end_time": (constraints["Mary"]["start_time"] + timedelta(minutes=constraints["Mary"]["meeting_duration"])).strftime("%H:%M")
        })
        current_time = constraints["Mary"]["start_time"] + timedelta(minutes=constraints["Mary"]["meeting_duration"])
        current_location = "Golden Gate Park"

    # Travel to Haight-Ashbury
    if current_time < datetime(2024, 7, 26, 10, 15):
        travel_time = 0
        for location in ["Embarcadero", "Golden Gate Park", current_location]:
            if location in travel_distances and "Golden Gate Park" in travel_distances[location]:
                travel_time += travel_distances[location]["Golden Gate Park"]
            elif location in travel_distances and current_location in travel_distances[location]:
                travel_time += travel_distances[location][current_location]
        current_time += timedelta(minutes=travel_time)
        current_location = "Golden Gate Park"

    # Meet Kevin
    if current_time < datetime(2024, 7, 26, 10, 15) + timedelta(minutes=constraints["Kevin"]["meeting_duration"]):
        itinerary.append({
            "action": "meet",
            "location": "Haight-Ashbury",
            "person": "Kevin",
            "start_time": datetime(2024, 7, 26, 10, 15).strftime("%H:%M"),
            "end_time": (datetime(2024, 7, 26, 10, 15) + timedelta(minutes=constraints["Kevin"]["meeting_duration"])).strftime("%H:%M")
        })
        current_time = datetime(2024, 7, 26, 10, 15) + timedelta(minutes=constraints["Kevin"]["meeting_duration"])
        current_location = "Haight-Ashbury"

    # Travel to Bayview
    if current_time < datetime(2024, 7, 26, 11, 30):
        travel_time = 0
        for location in ["Haight-Ashbury", current_location]:
            if location in travel_distances and "Bayview" in travel_distances[location]:
                travel_time += travel_distances[location]["Bayview"]
            elif location in travel_distances and "Bayview" in travel_distances:
                travel_time += travel_distances["Bayview"][location]
        current_time += timedelta(minutes=travel_time)
        current_location = "Bayview"

    # Meet Deborah
    if current_time < datetime(2024, 7, 26, 11, 30) + timedelta(minutes=constraints["Deborah"]["meeting_duration"]):
        itinerary.append({
            "action": "meet",
            "location": "Bayview",
            "person": "Deborah",
            "start_time": datetime(2024, 7, 26, 11, 30).strftime("%H:%M"),
            "end_time": (datetime(2024, 7, 26, 11, 30) + timedelta(minutes=constraints["Deborah"]["meeting_duration"])).strftime("%H:%M")
        })
        current_time = datetime(2024, 7, 26, 11, 30) + timedelta(minutes=constraints["Deborah"]["meeting_duration"])
        current_location = "Bayview"

    # Travel to Presidio
    if current_time < datetime(2024, 7, 26, 13, 30):
        travel_time = 0
        for location in ["Bayview", current_location]:
            if location in travel_distances and "Presidio" in travel_distances[location]:
                travel_time += travel_distances[location]["Presidio"]
            elif location in travel_distances and "Presidio" in travel_distances:
                travel_time += travel_distances["Presidio"][location]
        current_time += timedelta(minutes=travel_time)
        current_location = "Presidio"

    # Meet Stephanie
    if current_time < datetime(2024, 7, 26, 13, 30) + timedelta(minutes=constraints["Stephanie"]["meeting_duration"]):
        itinerary.append({
            "action": "meet",
            "location": "Presidio",
            "person": "Stephanie",
            "start_time": datetime(2024, 7, 26, 13, 30).strftime("%H:%M"),
            "end_time": (datetime(2024, 7, 26, 13, 30) + timedelta(minutes=constraints["Stephanie"]["meeting_duration"])).strftime("%H:%M")
        })
        current_time = datetime(2024, 7, 26, 13, 30) + timedelta(minutes=constraints["Stephanie"]["meeting_duration"])
        current_location = "Presidio"

    # Travel to Financial District
    if current_time < datetime(2024, 7, 26, 15, 45):
        travel_time = 0
        for location in ["Presidio", current_location]:
            if location in travel_distances and "Financial District" in travel_distances[location]:
                travel_time += travel_distances[location]["Financial District"]
            elif location in travel_distances and "Financial District" in travel_distances:
                travel_time += travel_distances["Financial District"][location]
        current_time += timedelta(minutes=travel_time)
        current_location = "Financial District"

    # Meet Emily
    if current_time < datetime(2024, 7, 26, 15, 45) + timedelta(minutes=constraints["Emily"]["meeting_duration"]):
        itinerary.append({
            "action": "meet",
            "location": "Financial District",
            "person": "Emily",
            "start_time": datetime(2024, 7, 26, 15, 45).strftime("%H:%M"),
            "end_time": (datetime(2024, 7, 26, 15, 45) + timedelta(minutes=constraints["Emily"]["meeting_duration"])).strftime("%H:%M")
        })
        current_time = datetime(2024, 7, 26, 15, 45) + timedelta(minutes=constraints["Emily"]["meeting_duration"])

    return itinerary

def main():
    itinerary = compute_itinerary()
    print(json.dumps({"itinerary": itinerary}, indent=4))

if __name__ == "__main__":
    main()