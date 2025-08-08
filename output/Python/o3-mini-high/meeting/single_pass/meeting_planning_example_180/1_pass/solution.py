#!/usr/bin/env python3
import json
import itertools

# Helper function to convert time string "H:MM" to minutes since midnight
def time_str_to_minutes(time_str):
    parts = time_str.split(":")
    hour = int(parts[0])
    minute = int(parts[1])
    return hour * 60 + minute

# Helper function to convert minutes since midnight to time string "H:MM"
def minutes_to_time_str(minutes):
    hour = minutes // 60
    minute = minutes % 60
    return f"{hour}:{minute:02d}"

# Define travel times in minutes between locations as a dictionary with (from, to) keys
travel_times = {
    ("North Beach", "Mission District"): 18,
    ("North Beach", "The Castro"): 22,
    ("Mission District", "North Beach"): 17,
    ("Mission District", "The Castro"): 7,
    ("The Castro", "North Beach"): 20,
    ("The Castro", "Mission District"): 7
}

# Define friend meeting constraints and details
friends = [
    {
        "person": "James",
        "location": "Mission District",
        "avail_start": "12:45",
        "avail_end": "14:00",
        "min_duration": 75  # in minutes
    },
    {
        "person": "Robert",
        "location": "The Castro",
        "avail_start": "12:45",
        "avail_end": "15:15",
        "min_duration": 30  # in minutes
    }
]

# Function to attempt scheduling meetings for a given order of friends
def attempt_schedule(order):
    itinerary = []
    # Starting conditions: arriving at North Beach at 9:00
    current_time = time_str_to_minutes("9:00")
    current_location = "North Beach"
    
    for friend in order:
        # Calculate travel time from current location to friend's location
        travel_key = (current_location, friend["location"])
        if travel_key not in travel_times:
            return None  # route not defined
        travel_time = travel_times[travel_key]
        arrival_time = current_time + travel_time
        
        # Determine the friend's availability window
        friend_avail_start = time_str_to_minutes(friend["avail_start"])
        friend_avail_end = time_str_to_minutes(friend["avail_end"])
        
        # Meeting can only start when both you have arrived and the friend is available
        meeting_start = max(arrival_time, friend_avail_start)
        meeting_end = meeting_start + friend["min_duration"]
        
        # Check if the meeting fits within the friend's available time window
        if meeting_end > friend_avail_end:
            return None  # scheduling not possible in this order
        
        # Append the meeting event to the itinerary
        itinerary.append({
            "action": "meet",
            "location": friend["location"],
            "person": friend["person"],
            "start_time": minutes_to_time_str(meeting_start),
            "end_time": minutes_to_time_str(meeting_end)
        })
        
        # Update current time and location for the next meeting
        current_time = meeting_end
        current_location = friend["location"]
    
    return itinerary

def compute_optimal_schedule():
    best_schedule = None
    max_meetings = 0

    # Try all possible orders for meeting the friends
    for order in itertools.permutations(friends):
        schedule = attempt_schedule(order)
        if schedule is not None and len(schedule) > max_meetings:
            best_schedule = schedule
            max_meetings = len(schedule)
    
    return best_schedule

def main():
    optimal_itinerary = compute_optimal_schedule()
    # In case no schedule is found, return an empty itinerary.
    output = {"itinerary": optimal_itinerary if optimal_itinerary is not None else []}
    print(json.dumps(output, indent=2))

if __name__ == '__main__':
    main()