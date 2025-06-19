import json
from datetime import datetime, timedelta

def compute_travel_time(start_location, end_location, travel_distances):
    return travel_distances[f"{start_location}_{end_location}"]

def is_valid_schedule(itinerary, person, start_time, end_time):
    for i, event in enumerate(itinerary):
        if event["person"] == person and start_time < event["start_time"] and event["end_time"] < end_time:
            return False
    return True

def find_optimal_schedule(meeting_constraints, travel_distances):
    # Initialize the schedule with the initial arrival at Fisherman's Wharf
    schedule = [
        {"action": "arrive", "location": "Fisherman's Wharf", "person": None, "start_time": "09:00", "end_time": "09:00"}
    ]

    # Iterate over the possible locations and times to meet Melissa
    for start_time in range(9, 20):
        for end_time in range(10, 20):
            for location in ["Golden Gate Park", "Presidio", "Richmond District"]:
                travel_time = compute_travel_time("Fisherman's Wharf", location, travel_distances)
                if start_time + travel_time >= 8 and end_time <= 8:
                    new_schedule = schedule + [
                        {"action": "meet", "location": location, "person": "Melissa", "start_time": f"{start_time}:{travel_time}", "end_time": f"{end_time}:00"}
                    ]
                    if is_valid_schedule(new_schedule, "Melissa", 8, 20):
                        schedule = new_schedule

    # Iterate over the possible locations and times to meet Nancy
    for start_time in range(19, 23):
        for end_time in range(20, 23):
            for location in ["Golden Gate Park", "Presidio", "Richmond District"]:
                travel_time = compute_travel_time(location, "Fisherman's Wharf", travel_distances)
                if start_time - travel_time >= 19 and end_time <= 22:
                    new_schedule = schedule + [
                        {"action": "meet", "location": location, "person": "Nancy", "start_time": f"{start_time - travel_time}:00", "end_time": f"{end_time}:00"}
                    ]
                    if is_valid_schedule(new_schedule, "Nancy", 19, 23):
                        schedule = new_schedule

    # Iterate over the possible locations and times to meet Emily
    for start_time in range(16, 23):
        for end_time in range(17, 23):
            for location in ["Golden Gate Park", "Presidio", "Richmond District"]:
                travel_time = compute_travel_time(location, "Fisherman's Wharf", travel_distances)
                if start_time - travel_time >= 16 and end_time <= 22:
                    new_schedule = schedule + [
                        {"action": "meet", "location": location, "person": "Emily", "start_time": f"{start_time - travel_time}:00", "end_time": f"{end_time}:00"}
                    ]
                    if is_valid_schedule(new_schedule, "Emily", 16, 23):
                        schedule = new_schedule

    return schedule

def main():
    travel_distances = {
        "Fisherman's Wharf_Golden Gate Park": 25,
        "Fisherman's Wharf_Presidio": 17,
        "Fisherman's Wharf_Richmond District": 18,
        "Golden Gate Park_Fisherman's Wharf": 24,
        "Golden Gate Park_Presidio": 11,
        "Golden Gate Park_Richmond District": 7,
        "Presidio_Fisherman's Wharf": 19,
        "Presidio_Golden Gate Park": 12,
        "Presidio_Richmond District": 7,
        "Richmond District_Fisherman's Wharf": 18,
        "Richmond District_Golden Gate Park": 9,
        "Richmond District_Presidio": 7
    }

    meeting_constraints = {
        "Melissa": {"start_time": 8.5, "end_time": 20, "duration": 0.25},
        "Nancy": {"start_time": 19.75, "end_time": 22, "duration": 1.75},
        "Emily": {"start_time": 16.75, "end_time": 22, "duration": 2}
    }

    schedule = find_optimal_schedule(meeting_constraints, travel_distances)
    itinerary = []
    for event in schedule:
        if event["action"] == "meet":
            start_time = datetime.strptime(event["start_time"], "%H:%M")
            end_time = datetime.strptime(event["end_time"], "%H:%M")
            itinerary.append({
                "action": "meet",
                "location": event["location"],
                "person": event["person"],
                "start_time": start_time.strftime("%H:%M"),
                "end_time": end_time.strftime("%H:%M")
            })

    result = {"itinerary": itinerary}
    print(json.dumps(result, indent=4))

if __name__ == "__main__":
    main()