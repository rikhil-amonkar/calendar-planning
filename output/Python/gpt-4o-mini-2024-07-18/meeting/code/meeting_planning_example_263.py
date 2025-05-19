import json
from datetime import datetime, timedelta

# Travel distances in minutes
travel_times = {
    ("Bayview", "Embarcadero"): 19,
    ("Bayview", "Fisherman's Wharf"): 25,
    ("Bayview", "Financial District"): 19,
    ("Embarcadero", "Fisherman's Wharf"): 6,
    ("Embarcadero", "Financial District"): 5,
    ("Fisherman's Wharf", "Financial District"): 11,
}

# Meeting constraints
constraints = {
    "Betty": {
        "location": "Embarcadero",
        "available_from": datetime.strptime("19:45", "%H:%M"),
        "available_until": datetime.strptime("21:45", "%H:%M"),
        "min_meeting_duration": timedelta(minutes=15)
    },
    "Karen": {
        "location": "Fisherman's Wharf",
        "available_from": datetime.strptime("08:45", "%H:%M"),
        "available_until": datetime.strptime("15:00", "%H:%M"),
        "min_meeting_duration": timedelta(minutes=30)
    },
    "Anthony": {
        "location": "Financial District",
        "available_from": datetime.strptime("09:15", "%H:%M"),
        "available_until": datetime.strptime("21:30", "%H:%M"),
        "min_meeting_duration": timedelta(minutes=105)
    }
}

# Start time
start_time = datetime.strptime("09:00", "%H:%M")

# Itinerary to store meetings
itinerary = []

# Function to schedule meetings
def schedule_meetings():
    current_time = start_time

    # Meet Karen first
    travel_time_to_karen = travel_times[("Bayview", "Fisherman's Wharf")]
    current_time += timedelta(minutes=travel_time_to_karen)
    
    # Calculate meeting time for Karen
    if current_time < constraints["Karen"]["available_from"]:
        current_time = constraints["Karen"]["available_from"]
    
    # Schedule meeting with Karen
    end_time_karen = current_time + constraints["Karen"]["min_meeting_duration"]
    if end_time_karen > constraints["Karen"]["available_until"]:
        end_time_karen = constraints["Karen"]["available_until"]

    itinerary.append({
        "action": "meet",
        "location": constraints["Karen"]["location"],
        "person": "Karen",
        "start_time": current_time.strftime("%H:%M"),
        "end_time": end_time_karen.strftime("%H:%M")
    })

    # Move to Embarcadero to meet Betty
    travel_time_to_betty = travel_times[("Fisherman's Wharf", "Embarcadero")]
    current_time = end_time_karen + timedelta(minutes=travel_time_to_betty)

    # Calculate meeting time for Betty
    if current_time < constraints["Betty"]["available_from"]:
        current_time = constraints["Betty"]["available_from"]

    # Schedule meeting with Betty
    end_time_betty = current_time + constraints["Betty"]["min_meeting_duration"]
    if end_time_betty > constraints["Betty"]["available_until"]:
        end_time_betty = constraints["Betty"]["available_until"]

    itinerary.append({
        "action": "meet",
        "location": constraints["Betty"]["location"],
        "person": "Betty",
        "start_time": current_time.strftime("%H:%M"),
        "end_time": end_time_betty.strftime("%H:%M"),
    })

    # Move to Financial District to meet Anthony
    travel_time_to_anthony = travel_times[("Embarcadero", "Financial District")]
    current_time = end_time_betty + timedelta(minutes=travel_time_to_anthony)

    # Calculate meeting time for Anthony
    if current_time < constraints["Anthony"]["available_from"]:
        current_time = constraints["Anthony"]["available_from"]

    # Schedule meeting with Anthony
    end_time_anthony = current_time + constraints["Anthony"]["min_meeting_duration"]
    if end_time_anthony > constraints["Anthony"]["available_until"]:
        end_time_anthony = constraints["Anthony"]["available_until"]

    itinerary.append({
        "action": "meet",
        "location": constraints["Anthony"]["location"],
        "person": "Anthony",
        "start_time": current_time.strftime("%H:%M"),
        "end_time": end_time_anthony.strftime("%H:%M"),
    })

schedule_meetings()

# Convert itinerary to JSON format
result = {"itinerary": itinerary}
print(json.dumps(result, indent=2))