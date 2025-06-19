import json
from datetime import datetime, timedelta

# Travel distances in minutes
travel_distances = {
    ("Nob Hill", "Presidio"): 17,
    ("Nob Hill", "North Beach"): 8,
    ("Nob Hill", "Fisherman's Wharf"): 11,
    ("Nob Hill", "Pacific Heights"): 8,
    ("Presidio", "Nob Hill"): 18,
    ("Presidio", "North Beach"): 18,
    ("Presidio", "Fisherman's Wharf"): 19,
    ("Presidio", "Pacific Heights"): 11,
    ("North Beach", "Nob Hill"): 7,
    ("North Beach", "Presidio"): 17,
    ("North Beach", "Fisherman's Wharf"): 5,
    ("North Beach", "Pacific Heights"): 8,
    ("Fisherman's Wharf", "Nob Hill"): 11,
    ("Fisherman's Wharf", "Presidio"): 17,
    ("Fisherman's Wharf", "North Beach"): 6,
    ("Fisherman's Wharf", "Pacific Heights"): 12,
    ("Pacific Heights", "Nob Hill"): 8,
    ("Pacific Heights", "Presidio"): 11,
    ("Pacific Heights", "North Beach"): 9,
    ("Pacific Heights", "Fisherman's Wharf"): 13,
}

# Meeting constraints
constraints = {
    "Jeffrey": {"location": "Presidio", "start_time": "08:00", "end_time": "10:00", "duration": 105},
    "Steven": {"location": "North Beach", "start_time": "13:30", "end_time": "22:00", "duration": 45},
    "Barbara": {"location": "Fisherman's Wharf", "start_time": "18:00", "end_time": "21:30", "duration": 30},
    "John": {"location": "Pacific Heights", "start_time": "09:00", "end_time": "13:30", "duration": 15},
}

# Arrival time
arrival_time = "09:00"

def compute_travel_time(start_location, end_location):
    return travel_distances[(start_location, end_location)]

def compute_meeting_schedule():
    schedule = []
    current_time = datetime.strptime(arrival_time, "%H:%M")
    locations = ["Nob Hill"]

    for person, constraint in constraints.items():
        start_time = datetime.strptime(constraint["start_time"], "%H:%M")
        end_time = datetime.strptime(constraint["end_time"], "%H:%M")

        # Check if current time is before the start time of the meeting
        if current_time < start_time:
            # Travel to meeting location
            travel_time = compute_travel_time(locations[-1], constraint["location"])
            current_time += timedelta(minutes=travel_time)

            # Wait until meeting starts
            wait_time = (start_time - current_time).total_seconds() / 60
            current_time += timedelta(minutes=wait_time)

            # Meet with person
            schedule.append({
                "action": "meet",
                "location": constraint["location"],
                "person": person,
                "start_time": start_time.strftime("%H:%M"),
                "end_time": (start_time + timedelta(minutes=constraint["duration"])).strftime("%H:%M"),
            })

            # Travel back to Nob Hill
            travel_time = compute_travel_time(constraint["location"], "Nob Hill")
            current_time += timedelta(minutes=travel_time)

            locations.append(constraint["location"])

        elif current_time < end_time:
            # Meet with person
            schedule.append({
                "action": "meet",
                "location": locations[-1],
                "person": person,
                "start_time": current_time.strftime("%H:%M"),
                "end_time": (current_time + timedelta(minutes=constraint["duration"])).strftime("%H:%M"),
            })

            # Travel to next location
            if person == "John":
                break

            # Check if Jeffrey's meeting time is outside his availability
            if person == "Jeffrey" and current_time < datetime.strptime("10:00", "%H:%M"):
                # If Jeffrey's meeting time is outside his availability, skip this meeting
                continue

            # Travel to next location
            travel_time = compute_travel_time(locations[-1], constraint["location"])
            current_time += timedelta(minutes=travel_time)

            locations.append(constraint["location"])

    return schedule

def main():
    schedule = compute_meeting_schedule()
    print(json.dumps({"itinerary": schedule}, indent=4))

if __name__ == "__main__":
    main()