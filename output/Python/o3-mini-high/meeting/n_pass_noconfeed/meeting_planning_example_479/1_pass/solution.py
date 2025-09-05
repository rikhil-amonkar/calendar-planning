import json
import itertools

# Convert a time in minutes from midnight to a string in H:MM format.
def convert_to_time_str(total_minutes):
    hour = total_minutes // 60
    minute = total_minutes % 60
    return f"{hour}:{minute:02d}"

# Define travel times (in minutes) between locations
travel_times = {
    "Embarcadero": {
        "Golden Gate Park": 25,
        "Haight-Ashbury": 21,
        "Bayview": 21,
        "Presidio": 20,
        "Financial District": 5
    },
    "Golden Gate Park": {
        "Embarcadero": 25,
        "Haight-Ashbury": 7,
        "Bayview": 23,
        "Presidio": 11,
        "Financial District": 26
    },
    "Haight-Ashbury": {
        "Embarcadero": 20,
        "Golden Gate Park": 7,
        "Bayview": 18,
        "Presidio": 15,
        "Financial District": 21
    },
    "Bayview": {
        "Embarcadero": 19,
        "Golden Gate Park": 22,
        "Haight-Ashbury": 19,
        "Presidio": 31,
        "Financial District": 19
    },
    "Presidio": {
        "Embarcadero": 20,
        "Golden Gate Park": 12,
        "Haight-Ashbury": 15,
        "Bayview": 31,
        "Financial District": 23
    },
    "Financial District": {
        "Embarcadero": 4,
        "Golden Gate Park": 23,
        "Haight-Ashbury": 19,
        "Bayview": 19,
        "Presidio": 22
    }
}

# Define meeting constraints for each friend.
# Times are represented as minutes from midnight.
# For example, 9:00 AM is 9*60 = 540.
meetings = [
    {
        "name": "Mary",
        "location": "Golden Gate Park",
        "window_start": 8 * 60 + 45,   # 8:45 AM
        "window_end": 11 * 60 + 45,      # 11:45 AM
        "duration": 45
    },
    {
        "name": "Kevin",
        "location": "Haight-Ashbury",
        "window_start": 10 * 60 + 15,  # 10:15 AM
        "window_end": 16 * 60 + 15,      # 4:15 PM
        "duration": 90
    },
    {
        "name": "Deborah",
        "location": "Bayview",
        "window_start": 15 * 60 + 0,   # 15:00 (3:00 PM)
        "window_end": 19 * 60 + 15,      # 19:15 (7:15 PM)
        "duration": 120
    },
    {
        "name": "Stephanie",
        "location": "Presidio",
        "window_start": 10 * 60 + 0,   # 10:00 AM
        "window_end": 17 * 60 + 15,      # 17:15 (5:15 PM)
        "duration": 120
    },
    {
        "name": "Emily",
        "location": "Financial District",
        "window_start": 11 * 60 + 30,  # 11:30 AM
        "window_end": 21 * 60 + 45,      # 21:45 (9:45 PM)
        "duration": 105
    }
]

# Starting point and time.
start_location = "Embarcadero"
start_time = 9 * 60  # 9:00 AM in minutes

# Function to compute a schedule for a given ordering of meetings.
def compute_schedule(order):
    current_time = start_time
    current_location = start_location
    itinerary = []
    for meeting in order:
        # Calculate travel time from the current location to the meeting location.
        if current_location == meeting["location"]:
            travel_time = 0
        else:
            travel_time = travel_times[current_location][meeting["location"]]
        arrival_time = current_time + travel_time
        # The meeting can only start when both you have arrived and the friend is available.
        meeting_start = max(arrival_time, meeting["window_start"])
        meeting_end = meeting_start + meeting["duration"]
        # Check if the meeting can be completed before the friend’s availability window closes.
        if meeting_end > meeting["window_end"]:
            return None  # This ordering is not feasible.
        # Add the meeting event to the itinerary.
        itinerary.append({
            "action": "meet",
            "location": meeting["location"],
            "person": meeting["name"],
            "start_time": convert_to_time_str(meeting_start),
            "end_time": convert_to_time_str(meeting_end)
        })
        # Update current time and location for the next meeting.
        current_time = meeting_end
        current_location = meeting["location"]
    return itinerary

# Iterate over all possible orderings of the meetings to find the optimal schedule.
# Optimality here is defined by the maximum number of meetings met.
# In case of a tie, we select the schedule with the earliest finishing time.
best_schedule = None
max_meetings = 0
best_finish_time = None

for order in itertools.permutations(meetings):
    schedule = compute_schedule(order)
    if schedule is not None:
        meeting_count = len(schedule)
        # Recompute the finish time of this schedule.
        current_time = start_time
        current_location = start_location
        for meeting in order:
            travel_time = travel_times[current_location][meeting["location"]] if current_location != meeting["location"] else 0
            arrival_time = current_time + travel_time
            meeting_start = max(arrival_time, meeting["window_start"])
            meeting_end = meeting_start + meeting["duration"]
            current_time = meeting_end
            current_location = meeting["location"]
        finish_time = current_time
        if (meeting_count > max_meetings) or (meeting_count == max_meetings and (best_finish_time is None or finish_time < best_finish_time)):
            best_schedule = schedule
            max_meetings = meeting_count
            best_finish_time = finish_time

# Prepare the result dictionary.
result = {"itinerary": best_schedule if best_schedule is not None else []}

# Output the schedule as JSON.
print(json.dumps(result, indent=2))