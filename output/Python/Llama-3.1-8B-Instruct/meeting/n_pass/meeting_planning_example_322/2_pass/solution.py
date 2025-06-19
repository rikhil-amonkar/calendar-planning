import json
from datetime import datetime, timedelta

# Travel distances (in minutes)
travel_distances = {
    "Sunset District to Russian Hill": 24,
    "Sunset District to Chinatown": 30,
    "Sunset District to Presidio": 16,
    "Sunset District to Fisherman's Wharf": 29,
    "Russian Hill to Sunset District": 23,
    "Russian Hill to Chinatown": 9,
    "Russian Hill to Presidio": 14,
    "Russian Hill to Fisherman's Wharf": 7,
    "Chinatown to Sunset District": 29,
    "Chinatown to Russian Hill": 7,
    "Chinatown to Presidio": 19,
    "Chinatown to Fisherman's Wharf": 8,
    "Presidio to Sunset District": 15,
    "Presidio to Russian Hill": 14,
    "Presidio to Chinatown": 21,
    "Presidio to Fisherman's Wharf": 19,
    "Fisherman's Wharf to Sunset District": 27,
    "Fisherman's Wharf to Russian Hill": 7,
    "Fisherman's Wharf to Chinatown": 12,
    "Fisherman's Wharf to Presidio": 17
}

# Constraints
start_time = datetime.strptime("09:00", "%H:%M")
william_start = datetime.strptime("18:30", "%H:%M")
william_end = datetime.strptime("20:45", "%H:%M")
william_duration = timedelta(minutes=105)  # Convert minutes to timedelta
michelle_start = datetime.strptime("08:15", "%H:%M")
michelle_end = datetime.strptime("14:00", "%H:%M")
michelle_duration = timedelta(minutes=15)  # Convert minutes to timedelta
george_start = datetime.strptime("10:30", "%H:%M")
george_end = datetime.strptime("18:45", "%H:%M")
george_duration = timedelta(minutes=30)  # Convert minutes to timedelta
robert_start = datetime.strptime("09:00", "%H:%M")
robert_end = datetime.strptime("13:45", "%H:%M")
robert_duration = timedelta(minutes=30)  # Convert minutes to timedelta

# Function to calculate travel time
def travel_time(from_location, to_location):
    travel_time = travel_distances[f"{from_location} to {to_location}"]
    return timedelta(minutes=travel_time)

# Function to add event to itinerary
def add_event(itinerary, action, location, person, start_time, end_time):
    event = {
        "action": action,
        "location": location,
        "person": person,
        "start_time": start_time.strftime("%H:%M"),
        "end_time": end_time.strftime("%H:%M")
    }
    itinerary.append(event)

# Main function to generate optimal schedule
def generate_schedule():
    itinerary = []
    current_time = start_time

    # Meet Michelle
    if current_time + michelle_duration <= michelle_start:
        add_event(itinerary, "meet", "Chinatown", "Michelle", current_time.strftime("%H:%M"), (current_time + michelle_duration).strftime("%H:%M"))
        current_time += michelle_duration
    elif michelle_start <= current_time <= michelle_end:
        add_event(itinerary, "meet", "Chinatown", "Michelle", current_time.strftime("%H:%M"), michelle_end.strftime("%H:%M"))
        current_time = michelle_end

    # Meet Robert
    if current_time + robert_duration <= robert_start:
        add_event(itinerary, "meet", "Fisherman's Wharf", "Robert", current_time.strftime("%H:%M"), (current_time + robert_duration).strftime("%H:%M"))
        current_time += robert_duration
    elif robert_start <= current_time <= robert_end:
        add_event(itinerary, "meet", "Fisherman's Wharf", "Robert", current_time.strftime("%H:%M"), robert_end.strftime("%H:%M"))
        current_time = robert_end

    # Meet George
    if current_time + george_duration <= george_start:
        add_event(itinerary, "meet", "Presidio", "George", current_time.strftime("%H:%M"), (current_time + george_duration).strftime("%H:%M"))
        current_time += george_duration
    elif george_start <= current_time <= george_end:
        add_event(itinerary, "meet", "Presidio", "George", current_time.strftime("%H:%M"), george_end.strftime("%H:%M"))
        current_time = george_end

    # Travel to William
    if current_time < william_start:
        travel_time_to_william = (william_start - current_time).total_seconds() / 60
        add_event(itinerary, "travel", "Sunset District", "William", current_time.strftime("%H:%M"), (current_time + timedelta(minutes=travel_time_to_william)).strftime("%H:%M"))
        current_time += timedelta(minutes=travel_time_to_william)

    # Meet William
    if current_time + william_duration <= william_end:
        add_event(itinerary, "meet", "Russian Hill", "William", current_time.strftime("%H:%M"), (current_time + william_duration).strftime("%H:%M"))
        current_time += william_duration
    elif william_start <= current_time <= william_end:
        add_event(itinerary, "meet", "Russian Hill", "William", current_time.strftime("%H:%M"), william_end.strftime("%H:%M"))
        current_time = william_end

    return itinerary

# Generate and print schedule
schedule = generate_schedule()
print(json.dumps({"itinerary": schedule}, indent=4))