import json
from datetime import datetime, timedelta

# Define constants
START_TIME = datetime.strptime("9:00", "%H:%M")
TRAVEL_TIMES = {
    ("Financial District", "Chinatown"): 5,
    ("Financial District", "Golden Gate Park"): 23,
    ("Chinatown", "Financial District"): 5,
    ("Chinatown", "Golden Gate Park"): 23,
    ("Golden Gate Park", "Financial District"): 26,
    ("Golden Gate Park", "Chinatown"): 23
}

FRIEND_AVAILABILITY = {
    "Kenneth": (datetime.strptime("12:00", "%H:%M"), datetime.strptime("15:00", "%H:%M"), timedelta(minutes=90)),
    "Barbara": (datetime.strptime("8:15", "%H:%M"), datetime.strptime("19:00", "%H:%M"), timedelta(minutes=45))
}

def can_meet(start_time, end_time, availability):
    return start_time >= availability[0] and end_time <= availability[1]

def format_time(time):
    return time.strftime("%H:%M").lstrip('0')

def calculate_itinerary():
    best_itinerary = []
    best_duration = timedelta(0)

    # Possible sequences of visits
    sequences = [
        ("Financial District", "Chinatown", "Golden Gate Park"),
        ("Financial District", "Golden Gate Park", "Chinatown"),
        ("Chinatown", "Financial District", "Golden Gate Park"),
        ("Chinatown", "Golden Gate Park", "Financial District"),
        ("Golden Gate Park", "Financial District", "Chinatown"),
        ("Golden Gate Park", "Chinatown", "Financial District")
    ]

    for sequence in sequences:
        current_time = START_TIME
        itinerary = []
        total_meeting_time = timedelta(0)

        for i, location in enumerate(sequence):
            if i == 0:
                # Starting point
                pass
            else:
                # Add travel time
                prev_location = sequence[i-1]
                travel_time = TRAVEL_TIMES[(prev_location, location)]
                current_time += timedelta(minutes=travel_time)

            # Check for meeting opportunities
            for friend, (start, end, min_duration) in FRIEND_AVAILABILITY.items():
                if location == "Chinatown" and friend == "Kenneth":
                    if can_meet(current_time, current_time + min_duration, (start, end)):
                        itinerary.append({
                            "action": "meet",
                            "location": location,
                            "person": friend,
                            "start_time": format_time(current_time),
                            "end_time": format_time(current_time + min_duration)
                        })
                        current_time += min_duration
                        total_meeting_time += min_duration
                elif location == "Golden Gate Park" and friend == "Barbara":
                    if can_meet(current_time, current_time + min_duration, (start, end)):
                        itinerary.append({
                            "action": "meet",
                            "location": location,
                            "person": friend,
                            "start_time": format_time(current_time),
                            "end_time": format_time(current_time + min_duration)
                        })
                        current_time += min_duration
                        total_meeting_time += min_duration

        # Update best itinerary if this one is better
        if total_meeting_time > best_duration:
            best_itinerary = itinerary
            best_duration = total_meeting_time

    return {"itinerary": best_itinerary}

# Calculate and print the optimal itinerary
optimal_itinerary = calculate_itinerary()
print(json.dumps(optimal_itinerary, indent=2))