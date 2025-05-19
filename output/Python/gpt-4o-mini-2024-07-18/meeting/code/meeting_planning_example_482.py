import json
from datetime import datetime, timedelta

# Define travel times (in minutes)
travel_times = {
    ("Haight-Ashbury", "Mission District"): 11,
    ("Haight-Ashbury", "Bayview"): 18,
    ("Haight-Ashbury", "Pacific Heights"): 12,
    ("Haight-Ashbury", "Russian Hill"): 17,
    ("Haight-Ashbury", "Fisherman's Wharf"): 23,
    ("Mission District", "Haight-Ashbury"): 12,
    ("Mission District", "Bayview"): 15,
    ("Mission District", "Pacific Heights"): 16,
    ("Mission District", "Russian Hill"): 15,
    ("Mission District", "Fisherman's Wharf"): 22,
    ("Bayview", "Haight-Ashbury"): 19,
    ("Bayview", "Mission District"): 13,
    ("Bayview", "Pacific Heights"): 23,
    ("Bayview", "Russian Hill"): 23,
    ("Bayview", "Fisherman's Wharf"): 25,
    ("Pacific Heights", "Haight-Ashbury"): 11,
    ("Pacific Heights", "Mission District"): 15,
    ("Pacific Heights", "Bayview"): 22,
    ("Pacific Heights", "Russian Hill"): 7,
    ("Pacific Heights", "Fisherman's Wharf"): 13,
    ("Russian Hill", "Haight-Ashbury"): 17,
    ("Russian Hill", "Mission District"): 16,
    ("Russian Hill", "Bayview"): 23,
    ("Russian Hill", "Pacific Heights"): 7,
    ("Russian Hill", "Fisherman's Wharf"): 7,
    ("Fisherman's Wharf", "Haight-Ashbury"): 22,
    ("Fisherman's Wharf", "Mission District"): 22,
    ("Fisherman's Wharf", "Bayview"): 26,
    ("Fisherman's Wharf", "Pacific Heights"): 12,
    ("Fisherman's Wharf", "Russian Hill"): 7,
}

# Define meeting constraints
constraints = {
    "Stephanie": {"location": "Mission District", "available": (datetime(2023, 1, 1, 8, 15), datetime(2023, 1, 1, 13, 45)), "duration": 90},
    "Sandra": {"location": "Bayview", "available": (datetime(2023, 1, 1, 13, 0), datetime(2023, 1, 1, 19, 30)), "duration": 15},
    "Richard": {"location": "Pacific Heights", "available": (datetime(2023, 1, 1, 7, 15), datetime(2023, 1, 1, 10, 15)), "duration": 75},
    "Brian": {"location": "Russian Hill", "available": (datetime(2023, 1, 1, 12, 15), datetime(2023, 1, 1, 16, 0)), "duration": 120},
    "Jason": {"location": "Fisherman's Wharf", "available": (datetime(2023, 1, 1, 8, 30), datetime(2023, 1, 1, 17, 45)), "duration": 60},
}

# Helper function to add minutes to a time
def add_minutes(start_time, minutes):
    return start_time + timedelta(minutes=minutes)

# Starting point
current_time = datetime(2023, 1, 1, 9, 0)  # Start at Haight-Ashbury at 9:00 AM
itinerary = []

def schedule_meeting(person, current_time):
    meeting_info = constraints[person]
    location = meeting_info["location"]
    start_time_window, end_time_window = meeting_info["available"]
    duration = meeting_info["duration"]
    
    travel_time = travel_times[(current_time.strftime("%A"), location)] if (current_time.strftime("%A"), location) in travel_times else None
    if travel_time is None:
        # Reverse travel time lookup
        travel_time = travel_times.get((location, current_time.strftime("%A")), None)
    
    if travel_time is not None:
        arrival_time = current_time + timedelta(minutes=travel_time)
        meeting_start_time = max(arrival_time, start_time_window)
        meeting_end_time = meeting_start_time + timedelta(minutes=duration)
        
        if meeting_end_time <= end_time_window:
            # Add meeting to itinerary
            itinerary.append({
                "action": "meet",
                "location": location,
                "person": person,
                "start_time": meeting_start_time.strftime("%H:%M"),
                "end_time": meeting_end_time.strftime("%H:%M"),
            })
            # Update the current time
            return meeting_end_time
    return current_time

# Schedule meetings
current_time = schedule_meeting("Richard", current_time)  # Meet Richard first
current_time = schedule_meeting("Stephanie", current_time)  # Meet Stephanie next
current_time = schedule_meeting("Jason", current_time)      # Meet Jason next
current_time = schedule_meeting("Brian", current_time)      # Meet Brian next
current_time = schedule_meeting("Sandra", current_time)     # Meet Sandra last

# Output the final itinerary as JSON
output = {"itinerary": itinerary}
print(json.dumps(output, indent=2))