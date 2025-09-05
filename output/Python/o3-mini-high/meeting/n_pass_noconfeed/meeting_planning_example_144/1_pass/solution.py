import itertools
import json

def time_to_minutes(time_str):
    # Converts a time string "H:MM" to minutes since midnight.
    parts = time_str.split(":")
    return int(parts[0]) * 60 + int(parts[1])

def minutes_to_time(minutes):
    # Converts minutes since midnight back to a time string "H:MM" (24-hour format with no leading zero for hour).
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

# Travel times between locations in minutes.
travel_times = {
    ("The Castro", "Mission District"): 7,
    ("The Castro", "Financial District"): 20,
    ("Mission District", "The Castro"): 7,
    ("Mission District", "Financial District"): 17,
    ("Financial District", "The Castro"): 23,
    ("Financial District", "Mission District"): 17
}

# Starting conditions.
start_location = "The Castro"
arrival_time_str = "9:00"   # Arrival at The Castro at 9:00 AM.
arrival_time = time_to_minutes(arrival_time_str)

# Meeting constraints for each friend.
meetings = [
    {
        "person": "Laura",
        "location": "Mission District",
        "avail_start": time_to_minutes("12:15"),  # Available from 12:15 PM
        "avail_end": time_to_minutes("19:45"),    # Available until 7:45 PM (19:45)
        "min_duration": 75                        # Minimum meeting duration: 75 minutes
    },
    {
        "person": "Anthony",
        "location": "Financial District",
        "avail_start": time_to_minutes("12:30"),  # Available from 12:30 PM
        "avail_end": time_to_minutes("14:45"),    # Available until 2:45 PM (14:45)
        "min_duration": 30                        # Minimum meeting duration: 30 minutes
    }
]

def simulate_schedule(order):
    itinerary = []
    current_time = arrival_time
    current_location = start_location
    
    # Simulate the schedule according to the order of meetings.
    for meeting in order:
        # Travel from current location to the meeting location.
        travel_duration = travel_times.get((current_location, meeting["location"]))
        if travel_duration is None:
            return None, None  # If travel path not defined.
        travel_arrival = current_time + travel_duration
        
        # Determine the meeting start time (must be no earlier than both arrival and the friend's available start).
        meeting_start = max(travel_arrival, meeting["avail_start"])
        meeting_end = meeting_start + meeting["min_duration"]
        
        # Check if the meeting can finish before the friend’s available end time.
        if meeting_end > meeting["avail_end"]:
            return None, None  # Schedule is not feasible.
        
        # Record the meeting event.
        event = {
            "action": "meet",
            "location": meeting["location"],
            "person": meeting["person"],
            "start_time": minutes_to_time(meeting_start),
            "end_time": minutes_to_time(meeting_end)
        }
        itinerary.append(event)
        
        # Update the current time and location for the next meeting.
        current_time = meeting_end
        current_location = meeting["location"]
    
    return itinerary, current_time

# Explore all orders of meeting the friends.
optimal_itinerary = None
optimal_finish = None

for order in itertools.permutations(meetings, len(meetings)):
    schedule, finish_time = simulate_schedule(order)
    if schedule is not None:
        # Choose the schedule that finishes earliest.
        if optimal_finish is None or finish_time < optimal_finish:
            optimal_finish = finish_time
            optimal_itinerary = schedule

result = {"itinerary": optimal_itinerary if optimal_itinerary is not None else []}

# Output the result as a JSON-formatted dictionary.
print(json.dumps(result, indent=2))