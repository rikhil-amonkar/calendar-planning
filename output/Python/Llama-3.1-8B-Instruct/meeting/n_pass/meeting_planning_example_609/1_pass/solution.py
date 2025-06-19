import json
from datetime import datetime, timedelta

# Travel distances in minutes
travel_distances = {
    "Chinatown": {
        "Mission District": 18,
        "Alamo Square": 17,
        "Pacific Heights": 10,
        "Union Square": 7,
        "Golden Gate Park": 23,
        "Sunset District": 29,
        "Presidio": 19,
    },
    "Mission District": {
        "Chinatown": 16,
        "Alamo Square": 11,
        "Pacific Heights": 16,
        "Union Square": 15,
        "Golden Gate Park": 17,
        "Sunset District": 24,
        "Presidio": 25,
    },
    "Alamo Square": {
        "Chinatown": 16,
        "Mission District": 10,
        "Pacific Heights": 10,
        "Union Square": 14,
        "Golden Gate Park": 9,
        "Sunset District": 16,
        "Presidio": 18,
    },
    "Pacific Heights": {
        "Chinatown": 11,
        "Mission District": 15,
        "Alamo Square": 10,
        "Union Square": 12,
        "Golden Gate Park": 15,
        "Sunset District": 21,
        "Presidio": 11,
    },
    "Union Square": {
        "Chinatown": 7,
        "Mission District": 14,
        "Alamo Square": 15,
        "Pacific Heights": 15,
        "Golden Gate Park": 22,
        "Sunset District": 26,
        "Presidio": 24,
    },
    "Golden Gate Park": {
        "Chinatown": 23,
        "Mission District": 17,
        "Alamo Square": 10,
        "Pacific Heights": 16,
        "Union Square": 22,
        "Sunset District": 10,
        "Presidio": 11,
    },
    "Sunset District": {
        "Chinatown": 30,
        "Mission District": 24,
        "Alamo Square": 17,
        "Pacific Heights": 21,
        "Union Square": 30,
        "Golden Gate Park": 11,
        "Presidio": 16,
    },
    "Presidio": {
        "Chinatown": 21,
        "Mission District": 26,
        "Alamo Square": 18,
        "Pacific Heights": 11,
        "Union Square": 22,
        "Golden Gate Park": 12,
        "Sunset District": 15,
    },
}

# Constraints
constraints = {
    "David": {"start_time": "08:00", "end_time": "19:45", "min_meeting_time": 45},
    "Kenneth": {"start_time": "14:00", "end_time": "19:45", "min_meeting_time": 120},
    "John": {"start_time": "17:00", "end_time": "20:00", "min_meeting_time": 15},
    "Charles": {"start_time": "21:45", "end_time": "22:45", "min_meeting_time": 60},
    "Deborah": {"start_time": "07:00", "end_time": "18:15", "min_meeting_time": 90},
    "Karen": {"start_time": "17:45", "end_time": "21:15", "min_meeting_time": 15},
    "Carol": {"start_time": "08:15", "end_time": "09:15", "min_meeting_time": 30},
}

def compute_meeting_schedule():
    # Start at Chinatown at 9:00 AM
    current_location = "Chinatown"
    current_time = "09:00"

    itinerary = []

    for person in constraints:
        start_time = datetime.strptime(constraints[person]["start_time"], "%H:%M")
        end_time = datetime.strptime(constraints[person]["end_time"], "%H:%M")

        # Check if person is available
        if start_time < datetime.strptime(current_time, "%H:%M") < end_time:
            # Calculate travel time
            travel_time = travel_distances[current_location][constraints[person]["location"]]

            # Calculate meeting start and end times
            meeting_start_time = datetime.strptime(current_time, "%H:%M") + timedelta(minutes=travel_time)
            meeting_end_time = meeting_start_time + timedelta(minutes=constraints[person]["min_meeting_time"])

            # Check if meeting end time is within person's availability
            if meeting_end_time <= end_time:
                # Add meeting to itinerary
                itinerary.append({
                    "action": "meet",
                    "location": constraints[person]["location"],
                    "person": person,
                    "start_time": meeting_start_time.strftime("%H:%M"),
                    "end_time": meeting_end_time.strftime("%H:%M"),
                })

                # Update current location and time
                current_location = constraints[person]["location"]
                current_time = meeting_end_time.strftime("%H:%M")

    return itinerary

def main():
    itinerary = compute_meeting_schedule()
    print(json.dumps({"itinerary": itinerary}, indent=4))

if __name__ == "__main__":
    main()