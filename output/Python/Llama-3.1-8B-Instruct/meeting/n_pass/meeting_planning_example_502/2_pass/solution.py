import json
from datetime import datetime, timedelta

# Travel distances in minutes
travel_distances = {
    ("Financial District", "Golden Gate Park"): 23,
    ("Financial District", "Chinatown"): 5,
    ("Financial District", "Union Square"): 9,
    ("Financial District", "Fisherman's Wharf"): 10,
    ("Financial District", "Pacific Heights"): 13,
    ("Financial District", "North Beach"): 7,
    ("Golden Gate Park", "Financial District"): 26,
    ("Golden Gate Park", "Chinatown"): 23,
    ("Golden Gate Park", "Union Square"): 22,
    ("Golden Gate Park", "Fisherman's Wharf"): 24,
    ("Golden Gate Park", "Pacific Heights"): 16,
    ("Golden Gate Park", "North Beach"): 24,
    ("Chinatown", "Financial District"): 5,
    ("Chinatown", "Golden Gate Park"): 23,
    ("Chinatown", "Union Square"): 7,
    ("Chinatown", "Fisherman's Wharf"): 8,
    ("Chinatown", "Pacific Heights"): 10,
    ("Chinatown", "North Beach"): 3,
    ("Union Square", "Financial District"): 9,
    ("Union Square", "Golden Gate Park"): 22,
    ("Union Square", "Chinatown"): 7,
    ("Union Square", "Fisherman's Wharf"): 15,
    ("Union Square", "Pacific Heights"): 15,
    ("Union Square", "North Beach"): 10,
    ("Fisherman's Wharf", "Financial District"): 11,
    ("Fisherman's Wharf", "Golden Gate Park"): 25,
    ("Fisherman's Wharf", "Chinatown"): 12,
    ("Fisherman's Wharf", "Union Square"): 13,
    ("Fisherman's Wharf", "Pacific Heights"): 12,
    ("Fisherman's Wharf", "North Beach"): 6,
    ("Pacific Heights", "Financial District"): 13,
    ("Pacific Heights", "Golden Gate Park"): 15,
    ("Pacific Heights", "Chinatown"): 11,
    ("Pacific Heights", "Union Square"): 12,
    ("Pacific Heights", "Fisherman's Wharf"): 13,
    ("Pacific Heights", "North Beach"): 9,
    ("North Beach", "Financial District"): 8,
    ("North Beach", "Golden Gate Park"): 22,
    ("North Beach", "Chinatown"): 6,
    ("North Beach", "Union Square"): 7,
    ("North Beach", "Fisherman's Wharf"): 5,
    ("North Beach", "Pacific Heights"): 8
}

# Meeting constraints
constraints = {
    "Stephanie": {"location": "Golden Gate Park", "start_time": 11, "end_time": 15, "duration": 105},
    "Karen": {"location": "Chinatown", "start_time": 14.75, "end_time": 16.5, "duration": 15},
    "Brian": {"location": "Union Square", "start_time": 15, "end_time": 17.25, "duration": 30},
    "Rebecca": {"location": "Fisherman's Wharf", "start_time": 8, "end_time": 10.25, "duration": 30},
    "Joseph": {"location": "Pacific Heights", "start_time": 8.25, "end_time": 9.5, "duration": 60},
    "Steven": {"location": "North Beach", "start_time": 14.5, "end_time": 20.75, "duration": 120}
}

def calculate_travel_time(location1, location2):
    return travel_distances.get((location1, location2), 0) / 60  # convert minutes to hours

def schedule_meetings():
    schedule = []
    current_time = 9  # 9:00 AM
    current_location = "Financial District"

    for person, constraint in constraints.items():
        location = constraint["location"]
        start_time = constraint["start_time"]
        end_time = constraint["end_time"]
        duration = constraint["duration"]

        # Calculate travel time to the meeting location
        travel_time = calculate_travel_time(current_location, location)
        meeting_start_time = max(current_time, start_time) + travel_time
        meeting_end_time = meeting_start_time + duration / 60  # convert minutes to hours

        # Check if the meeting can be scheduled
        if meeting_start_time >= start_time and meeting_end_time <= end_time:
            schedule.append({
                "action": "meet",
                "location": location,
                "person": person,
                "start_time": "{:02d}:{:02d}".format(int(meeting_start_time), int((meeting_start_time - int(meeting_start_time)) * 60)),
                "end_time": "{:02d}:{:02d}".format(int(meeting_end_time), int((meeting_end_time - int(meeting_end_time)) * 60))
            })

            # Update current location and time
            current_location = location
            current_time = meeting_end_time

    return schedule

def main():
    schedule = schedule_meetings()
    # Sort the schedule in chronological order
    schedule.sort(key=lambda x: (x['start_time'], x['location']))
    print(json.dumps({"itinerary": schedule}, indent=4))

if __name__ == "__main__":
    main()