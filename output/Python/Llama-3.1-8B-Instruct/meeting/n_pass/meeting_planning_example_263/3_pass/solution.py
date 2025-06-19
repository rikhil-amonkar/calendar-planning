import json
from datetime import datetime, timedelta

# Travel distances in minutes
travel_distances = {
    "Bayview": {
        "Embarcadero": 19,
        "Fisherman's Wharf": 25,
        "Financial District": 19
    },
    "Embarcadero": {
        "Bayview": 21,
        "Fisherman's Wharf": 6,
        "Financial District": 5
    },
    "Fisherman's Wharf": {
        "Bayview": 26,
        "Embarcadero": 8,
        "Financial District": 11
    },
    "Financial District": {
        "Bayview": 19,
        "Embarcadero": 4,
        "Fisherman's Wharf": 10
    }
}

# Meeting constraints
constraints = {
    "Betty": {
        "start_time": "19:45",
        "end_time": "21:45",
        "min_meeting_time": 15
    },
    "Karen": {
        "start_time": "08:45",
        "end_time": "15:00",
        "min_meeting_time": 30
    },
    "Anthony": {
        "start_time": "09:15",
        "end_time": "21:30",
        "min_meeting_time": 105
    }
}

def calculate_meeting_schedule():
    # Initialize the schedule
    schedule = []

    # Start at Bayview at 09:00
    current_location = "Bayview"
    current_time = datetime.strptime("09:00", "%H:%M")

    # Meet Karen at Fisherman's Wharf
    schedule.append({
        "action": "meet",
        "location": "Fisherman's Wharf",
        "person": "Karen",
        "start_time": current_time.strftime("%H:%M"),
        "end_time": (current_time + timedelta(minutes=travel_distances["Bayview"]["Fisherman's Wharf"] + 30)).strftime("%H:%M")
    })
    current_location = "Fisherman's Wharf"
    current_time = (current_time + timedelta(minutes=travel_distances["Bayview"]["Fisherman's Wharf"] + 30))

    # Meet Anthony at Financial District
    schedule.append({
        "action": "meet",
        "location": "Financial District",
        "person": "Anthony",
        "start_time": current_time.strftime("%H:%M"),
        "end_time": (current_time + timedelta(minutes=travel_distances["Fisherman's Wharf"]["Financial District"] + constraints["Anthony"]["min_meeting_time"])).strftime("%H:%M")
    })
    current_location = "Financial District"
    current_time = (current_time + timedelta(minutes=travel_distances["Fisherman's Wharf"]["Financial District"] + constraints["Anthony"]["min_meeting_time"]))

    # Travel to Embarcadero to meet Betty
    schedule.append({
        "action": "travel",
        "location": "Embarcadero",
        "person": "",
        "start_time": current_time.strftime("%H:%M"),
        "end_time": (current_time + timedelta(minutes=travel_distances["Financial District"]["Embarcadero"])).strftime("%H:%M")
    })
    current_location = "Embarcadero"
    current_time = (current_time + timedelta(minutes=travel_distances["Financial District"]["Embarcadero"]))

    # Meet Betty at Embarcadero
    if "Betty" in constraints:
        if current_time >= datetime.strptime(constraints["Betty"]["start_time"], "%H:%M") and current_time <= datetime.strptime(constraints["Betty"]["end_time"], "%H:%M"):
            schedule.append({
                "action": "meet",
                "location": "Embarcadero",
                "person": "Betty",
                "start_time": current_time.strftime("%H:%M"),
                "end_time": (current_time + timedelta(minutes=max(travel_distances["Embarcadero"]["Bayview"], constraints["Betty"]["min_meeting_time"]))).strftime("%H:%M")
            })
            current_time = (current_time + timedelta(minutes=max(travel_distances["Embarcadero"]["Bayview"], constraints["Betty"]["min_meeting_time"])))
        else:
            # If meeting time is outside Betty's availability, skip the meeting
            print("Meeting time with Betty is outside her availability. Skipping the meeting.")
    else:
        print("Betty's availability is not defined in the constraints.")

    # Return the schedule as JSON
    return json.dumps({"itinerary": schedule}, indent=4)

# Print the schedule
print("SOLUTION:")
print(calculate_meeting_schedule())