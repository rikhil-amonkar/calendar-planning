import json
from datetime import datetime, timedelta

# Travel distances (in minutes)
travel_times = {
    ("Embarcadero", "Fisherman's Wharf"): 6,
    ("Embarcadero", "Financial District"): 5,
    ("Embarcadero", "Russian Hill"): 8,
    ("Embarcadero", "Marina District"): 12,
    ("Embarcadero", "Richmond District"): 21,
    ("Embarcadero", "Pacific Heights"): 11,
    ("Embarcadero", "Haight-Ashbury"): 21,
    ("Embarcadero", "Presidio"): 20,
    ("Embarcadero", "Nob Hill"): 10,
    ("Embarcadero", "The Castro"): 25,
    ("Fisherman's Wharf", "Embarcadero"): 8,
    ("Fisherman's Wharf", "Financial District"): 11,
    ("Fisherman's Wharf", "Russian Hill"): 7,
    ("Fisherman's Wharf", "Marina District"): 9,
    ("Fisherman's Wharf", "Richmond District"): 18,
    ("Fisherman's Wharf", "Pacific Heights"): 12,
    ("Fisherman's Wharf", "Haight-Ashbury"): 22,
    ("Fisherman's Wharf", "Presidio"): 17,
    ("Fisherman's Wharf", "Nob Hill"): 11,
    ("Fisherman's Wharf", "The Castro"): 27,
    # Additional travel times ...
    # Add all other locations as specified in the problem
}

# Meeting constraints
meetings = {
    "Stephanie": {"location": "Fisherman's Wharf", "available_from": "15:30", "available_to": "22:00", "duration": 30},
    "Lisa": {"location": "Financial District", "available_from": "10:45", "available_to": "17:15", "duration": 15},
    "Melissa": {"location": "Russian Hill", "available_from": "17:00", "available_to": "21:45", "duration": 120},
    "Betty": {"location": "Marina District", "available_from": "10:45", "available_to": "14:15", "duration": 60},
    "Sarah": {"location": "Richmond District", "available_from": "16:15", "available_to": "19:30", "duration": 105},
    "Daniel": {"location": "Pacific Heights", "available_from": "18:30", "available_to": "21:45", "duration": 60},
    "Joshua": {"location": "Haight-Ashbury", "available_from": "09:00", "available_to": "15:30", "duration": 15},
    "Joseph": {"location": "Presidio", "available_from": "07:00", "available_to": "13:00", "duration": 45},
    "Andrew": {"location": "Nob Hill", "available_from": "19:45", "available_to": "22:00", "duration": 105},
    "John": {"location": "The Castro", "available_from": "13:15", "available_to": "19:45", "duration": 45},
}

start_time = datetime.strptime("09:00", "%H:%M")

def schedule_meetings(start_time):
    itinerary = []
    current_time = start_time
    visited_locations = set()

    # Function to convert string time to datetime object
    def convert_time(time_str):
        return datetime.strptime(time_str, "%H:%M")

    for person, details in meetings.items():
        available_from = convert_time(details["available_from"])
        available_to = convert_time(details["available_to"])
        duration = details["duration"]

        location = details["location"]
        travel_time = travel_times.get(("Embarcadero", location)) or travel_times.get((location, "Embarcadero"))

        # Meet Joshua first before he leaves
        if person == "Joshua":
            if current_time + timedelta(minutes=travel_time) <= available_to:
                end_time = current_time + timedelta(minutes=travel_time + duration)
                if end_time <= available_to:
                    itinerary.append({
                        "action": "meet",
                        "location": location,
                        "person": person,
                        "start_time": current_time.strftime("%H:%M"),
                        "end_time": end_time.strftime("%H:%M"),
                    })
                    current_time = end_time + timedelta(minutes=travel_time)  # Move back to Embarcadero
                    visited_locations.add(location)

    # Schedule other meetings
    for person, details in meetings.items():
        if person in visited_locations:
            continue  # Skip already visited locations
        available_from = convert_time(details["available_from"])
        available_to = convert_time(details["available_to"])
        duration = details["duration"]

        travel_time = travel_times.get(("Embarcadero", details["location"])) or travel_times.get((details["location"], "Embarcadero"))

        # Only meet if we can travel there and meet within available time
        if current_time + timedelta(minutes=travel_time) <= available_to:
            end_time = current_time + timedelta(minutes=travel_time + duration)
            if end_time <= available_to:
                itinerary.append({
                    "action": "meet",
                    "location": details["location"],
                    "person": person,
                    "start_time": current_time.strftime("%H:%M"),
                    "end_time": end_time.strftime("%H:%M"),
                })
                current_time = end_time + timedelta(minutes=travel_time)  # Return to Embarcadero

    return {"itinerary": itinerary}

optimal_schedule = schedule_meetings(start_time)
print(json.dumps(optimal_schedule, indent=2))