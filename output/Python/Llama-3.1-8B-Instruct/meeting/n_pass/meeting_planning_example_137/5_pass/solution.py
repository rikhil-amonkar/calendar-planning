import json
from datetime import datetime, timedelta

def calculate_travel_time(distance, speed=40):  # assume a speed of 40 km/h
    """Calculate travel time in minutes."""
    return (distance / speed) * 60

def compute_meeting_schedule():
    # Define travel distances
    travel_distances = {
        "Financial District to Chinatown": 5,
        "Financial District to Golden Gate Park": 23,
        "Chinatown to Financial District": 5,
        "Chinatown to Golden Gate Park": 23,
        "Golden Gate Park to Financial District": 26,
        "Golden Gate Park to Chinatown": 23
    }

    # Define meeting constraints
    start_time = datetime.strptime("09:00", "%H:%M")
    kenneth_start_time = datetime.strptime("12:00", "%H:%M")
    kenneth_end_time = datetime.strptime("15:00", "%H:%M")
    barbara_start_time = datetime.strptime("08:15", "%H:%M")
    barbara_end_time = datetime.strptime("19:00", "%H:%M")
    kenneth_meeting_duration = timedelta(minutes=90)
    barbara_meeting_duration = timedelta(minutes=45)

    # Initialize itinerary
    itinerary = []

    # Meet Barbara at Golden Gate Park
    barbara_meeting_start_time = barbara_start_time
    barbara_meeting_end_time = barbara_meeting_start_time + barbara_meeting_duration
    itinerary.append({
        "action": "meet",
        "location": "Golden Gate Park",
        "person": "Barbara",
        "start_time": barbara_meeting_start_time.strftime("%H:%M"),
        "end_time": barbara_meeting_end_time.strftime("%H:%M")
    })

    # Travel back to Financial District
    travel_time = calculate_travel_time(travel_distances["Golden Gate Park to Financial District"])
    if barbara_meeting_end_time + timedelta(minutes=travel_time) > barbara_end_time:
        travel_time = (barbara_end_time - barbara_meeting_end_time).total_seconds() / 60
    meeting_start_time = barbara_meeting_end_time + timedelta(minutes=travel_time)
    itinerary.append({
        "action": "travel",
        "location": "Financial District",
        "person": "",
        "start_time": meeting_start_time.strftime("%H:%M"),
        "end_time": (meeting_start_time + timedelta(minutes=1)).strftime("%H:%M")
    })

    # Travel to Chinatown
    travel_time = calculate_travel_time(travel_distances["Financial District to Chinatown"])
    if meeting_start_time + timedelta(minutes=travel_time) > kenneth_start_time:
        travel_time = (kenneth_start_time - meeting_start_time).total_seconds() / 60
    meeting_start_time = meeting_start_time + timedelta(minutes=travel_time)
    itinerary.append({
        "action": "travel",
        "location": "Chinatown",
        "person": "",
        "start_time": meeting_start_time.strftime("%H:%M"),
        "end_time": (meeting_start_time + timedelta(minutes=1)).strftime("%H:%M")
    })

    # Meet Kenneth at Chinatown
    kenneth_meeting_start_time = max(kenneth_start_time, meeting_start_time)  # Ensure Kenneth's meeting starts after the last travel
    kenneth_meeting_end_time = kenneth_meeting_start_time + kenneth_meeting_duration
    if kenneth_meeting_end_time > kenneth_end_time:
        kenneth_meeting_end_time = kenneth_end_time
        kenneth_meeting_start_time = kenneth_meeting_end_time - kenneth_meeting_duration
    itinerary.append({
        "action": "meet",
        "location": "Chinatown",
        "person": "Kenneth",
        "start_time": kenneth_meeting_start_time.strftime("%H:%M"),
        "end_time": kenneth_meeting_end_time.strftime("%H:%M")
    })

    # Return itinerary as JSON
    return json.dumps({"itinerary": itinerary}, indent=4)

# Compute and print meeting schedule
print(compute_meeting_schedule())