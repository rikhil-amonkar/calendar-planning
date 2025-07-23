import json
from itertools import permutations

def time_to_minutes(time_str):
    hours, minutes = map(int, time_str.split(':'))
    return hours * 60 + minutes

def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

def calculate_schedule():
    # Define travel times as a dictionary of dictionaries
    travel_times = {
        "Mission District": {
            "The Castro": 7,
            "Nob Hill": 12,
            "Presidio": 25,
            "Marina District": 19,
            "Pacific Heights": 16,
            "Golden Gate Park": 17,
            "Chinatown": 16,
            "Richmond District": 20
        },
        "The Castro": {
            "Mission District": 7,
            "Nob Hill": 16,
            "Presidio": 20,
            "Marina District": 21,
            "Pacific Heights": 16,
            "Golden Gate Park": 11,
            "Chinatown": 22,
            "Richmond District": 16
        },
        "Nob Hill": {
            "Mission District": 13,
            "The Castro": 17,
            "Presidio": 17,
            "Marina District": 11,
            "Pacific Heights": 8,
            "Golden Gate Park": 17,
            "Chinatown": 6,
            "Richmond District": 14
        },
        "Presidio": {
            "Mission District": 26,
            "The Castro": 21,
            "Nob Hill": 18,
            "Marina District": 11,
            "Pacific Heights": 11,
            "Golden Gate Park": 12,
            "Chinatown": 21,
            "Richmond District": 7
        },
        "Marina District": {
            "Mission District": 20,
            "The Castro": 22,
            "Nob Hill": 12,
            "Presidio": 10,
            "Pacific Heights": 7,
            "Golden Gate Park": 18,
            "Chinatown": 15,
            "Richmond District": 11
        },
        "Pacific Heights": {
            "Mission District": 15,
            "The Castro": 16,
            "Nob Hill": 8,
            "Presidio": 11,
            "Marina District": 6,
            "Golden Gate Park": 15,
            "Chinatown": 11,
            "Richmond District": 12
        },
        "Golden Gate Park": {
            "Mission District": 17,
            "The Castro": 13,
            "Nob Hill": 20,
            "Presidio": 11,
            "Marina District": 16,
            "Pacific Heights": 16,
            "Chinatown": 23,
            "Richmond District": 7
        },
        "Chinatown": {
            "Mission District": 17,
            "The Castro": 22,
            "Nob Hill": 9,
            "Presidio": 19,
            "Marina District": 12,
            "Pacific Heights": 10,
            "Golden Gate Park": 23,
            "Richmond District": 20
        },
        "Richmond District": {
            "Mission District": 20,
            "The Castro": 16,
            "Nob Hill": 17,
            "Presidio": 7,
            "Marina District": 9,
            "Pacific Heights": 10,
            "Golden Gate Park": 9,
            "Chinatown": 20
        }
    }

    # Define friends' availability and meeting requirements
    friends = [
        {
            "name": "Lisa",
            "location": "The Castro",
            "start": time_to_minutes("19:15"),
            "end": time_to_minutes("21:15"),
            "duration": 120
        },
        {
            "name": "Daniel",
            "location": "Nob Hill",
            "start": time_to_minutes("8:15"),
            "end": time_to_minutes("11:00"),
            "duration": 15
        },
        {
            "name": "Elizabeth",
            "location": "Presidio",
            "start": time_to_minutes("21:15"),
            "end": time_to_minutes("22:15"),
            "duration": 45
        },
        {
            "name": "Steven",
            "location": "Marina District",
            "start": time_to_minutes("16:30"),
            "end": time_to_minutes("20:45"),
            "duration": 90
        },
        {
            "name": "Timothy",
            "location": "Pacific Heights",
            "start": time_to_minutes("12:00"),
            "end": time_to_minutes("18:00"),
            "duration": 90
        },
        {
            "name": "Ashley",
            "location": "Golden Gate Park",
            "start": time_to_minutes("20:45"),
            "end": time_to_minutes("21:45"),
            "duration": 60
        },
        {
            "name": "Kevin",
            "location": "Chinatown",
            "start": time_to_minutes("12:00"),
            "end": time_to_minutes("19:00"),
            "duration": 30
        },
        {
            "name": "Betty",
            "location": "Richmond District",
            "start": time_to_minutes("13:15"),
            "end": time_to_minutes("15:45"),
            "duration": 30
        }
    ]

    # Start at Mission District at 9:00 AM
    current_time = time_to_minutes("9:00")
    current_location = "Mission District"
    itinerary = []

    # Sort friends by their end time to prioritize those with earlier deadlines
    friends_sorted = sorted(friends, key=lambda x: x["end"])

    for friend in friends_sorted:
        # Skip Lisa for now (we'll handle her separately)
        if friend["name"] == "Lisa":
            continue
            
        # Check if current_location exists in travel_times and has the friend's location
        if current_location in travel_times and friend["location"] in travel_times[current_location]:
            travel_time = travel_times[current_location][friend["location"]]
            arrival_time = current_time + travel_time

            # Check if we can meet the friend within their availability
            if arrival_time <= friend["end"] - friend["duration"]:
                start_time = max(arrival_time, friend["start"])
                end_time = start_time + friend["duration"]

                if end_time <= friend["end"]:
                    itinerary.append({
                        "action": "meet",
                        "location": friend["location"],
                        "person": friend["name"],
                        "start_time": minutes_to_time(start_time),
                        "end_time": minutes_to_time(end_time)
                    })
                    current_time = end_time
                    current_location = friend["location"]

    # Handle Lisa separately
    lisa = next(f for f in friends if f["name"] == "Lisa")
    if current_location in travel_times and lisa["location"] in travel_times[current_location]:
        travel_time = travel_times[current_location][lisa["location"]]
        arrival_time = current_time + travel_time
        if arrival_time <= lisa["end"] - lisa["duration"]:
            start_time = max(arrival_time, lisa["start"])
            end_time = start_time + lisa["duration"]
            if end_time <= lisa["end"]:
                itinerary.append({
                    "action": "meet",
                    "location": lisa["location"],
                    "person": lisa["name"],
                    "start_time": minutes_to_time(start_time),
                    "end_time": minutes_to_time(end_time)
                })

    return {"itinerary": itinerary}

if __name__ == "__main__":
    schedule = calculate_schedule()
    print(json.dumps(schedule, indent=2))