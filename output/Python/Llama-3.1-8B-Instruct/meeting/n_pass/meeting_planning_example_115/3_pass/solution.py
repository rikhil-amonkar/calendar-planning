import json
from datetime import datetime, timedelta

def compute_meeting_schedule():
    # Define travel distances (in minutes)
    travel_distances = {
        "Richmond District to Pacific Heights": 10,
        "Richmond District to Marina District": 9,
        "Pacific Heights to Richmond District": 12,
        "Pacific Heights to Marina District": 6,
        "Marina District to Richmond District": 11,
        "Marina District to Pacific Heights": 7
    }

    # Define constraints
    start_time = datetime.strptime("09:00", "%H:%M")
    jessica_available = (datetime.strptime("10:00", "%H:%M"), datetime.strptime("16:45", "%H:%M"))  # Adjusted Jessica's available time
    carol_available = (datetime.strptime("11:30", "%H:%M"), datetime.strptime("15:00", "%H:%M"))
    min_meeting_duration = {"Jessica": 45, "Carol": 60}

    # Initialize itinerary
    itinerary = []

    # Travel to Pacific Heights
    itinerary.append({"action": "travel", "location": "Pacific Heights", "person": "", "start_time": start_time.strftime("%H:%M"), "end_time": (start_time + timedelta(minutes=travel_distances["Richmond District to Pacific Heights"])).strftime("%H:%M")})

    # Meet Jessica
    jessica_start_time = max(jessica_available[0], start_time + timedelta(minutes=travel_distances["Richmond District to Pacific Heights"]))
    jessica_end_time = min(jessica_available[1], jessica_start_time + timedelta(minutes=min_meeting_duration["Jessica"]))  # Ensure meeting time does not exceed Jessica's available time
    itinerary.append({"action": "meet", "location": "Pacific Heights", "person": "Jessica", "start_time": jessica_start_time.strftime("%H:%M"), "end_time": jessica_end_time.strftime("%H:%M")})

    # Travel to Marina District
    itinerary.append({"action": "travel", "location": "Marina District", "person": "", "start_time": jessica_end_time.strftime("%H:%M"), "end_time": (jessica_end_time + timedelta(minutes=travel_distances["Pacific Heights to Marina District"])).strftime("%H:%M")})

    # Meet Carol
    carol_start_time = max(carol_available[0], jessica_end_time + timedelta(minutes=travel_distances["Pacific Heights to Marina District"]))
    if carol_start_time > carol_available[0]:
        carol_start_time = carol_available[0]
    carol_end_time = carol_start_time + timedelta(minutes=min_meeting_duration["Carol"])
    itinerary.append({"action": "meet", "location": "Marina District", "person": "Carol", "start_time": carol_start_time.strftime("%H:%M"), "end_time": carol_end_time.strftime("%H:%M")})

    # Return itinerary as JSON
    return json.dumps({"itinerary": itinerary})

print(compute_meeting_schedule())