#!/usr/bin/env python3
import json
import itertools

def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

def compute_schedule(order, travel_times, start_loc, start_time):
    schedule = []
    current_time = start_time
    current_loc = start_loc
    for meeting in order:
        # Get travel time from the current location to the meeting location
        travel_key = (current_loc, meeting["location"])
        if travel_key not in travel_times:
            return None  # travel time not defined
        travel = travel_times[travel_key]
        arrival_time = current_time + travel
        # Wait until the person's available start time if arriving early
        meeting_start = max(arrival_time, meeting["avail_start"])
        meeting_end = meeting_start + meeting["duration"]
        # Check if the meeting can be held within the person's available window
        if meeting_end > meeting["avail_end"]:
            return None
        event = {
            "action": "meet",
            "location": meeting["location"],
            "person": meeting["name"],
            "start_time": minutes_to_time(meeting_start),
            "end_time": minutes_to_time(meeting_end)
        }
        schedule.append(event)
        current_time = meeting_end
        current_loc = meeting["location"]
    return schedule, current_time

def main():
    # Define travel times in minutes between locations
    travel_times = {
        ("Fisherman's Wharf", "Presidio"): 17,
        ("Fisherman's Wharf", "Richmond District"): 18,
        ("Fisherman's Wharf", "Financial District"): 11,
        ("Presidio", "Fisherman's Wharf"): 19,
        ("Presidio", "Richmond District"): 7,
        ("Presidio", "Financial District"): 23,
        ("Richmond District", "Fisherman's Wharf"): 18,
        ("Richmond District", "Presidio"): 7,
        ("Richmond District", "Financial District"): 22,
        ("Financial District", "Fisherman's Wharf"): 10,
        ("Financial District", "Presidio"): 22,
        ("Financial District", "Richmond District"): 21
    }
    
    # Participants with their meeting constraints (times in minutes after midnight)
    participants = [
        {
            "name": "Emily",
            "location": "Presidio",
            "avail_start": 16 * 60 + 15,  # 16:15
            "avail_end": 21 * 60,         # 21:00
            "duration": 105
        },
        {
            "name": "Joseph",
            "location": "Richmond District",
            "avail_start": 17 * 60 + 15,  # 17:15
            "avail_end": 22 * 60,         # 22:00
            "duration": 120
        },
        {
            "name": "Melissa",
            "location": "Financial District",
            "avail_start": 15 * 60 + 45,  # 15:45
            "avail_end": 21 * 60 + 45,    # 21:45
            "duration": 75
        }
    ]
    
    start_location = "Fisherman's Wharf"
    start_time = 9 * 60  # 9:00 in minutes
    
    best_schedule = None
    best_finish_time = float('inf')
    
    # Evaluate all permutations of meeting orders
    for order in itertools.permutations(participants):
        result = compute_schedule(order, travel_times, start_location, start_time)
        if result is not None:
            schedule, finish_time = result
            # Choose the schedule that finishes the earliest (optimal in terms of time)
            if finish_time < best_finish_time:
                best_finish_time = finish_time
                best_schedule = schedule
    
    if best_schedule is None:
        output = {"itinerary": []}
    else:
        output = {"itinerary": best_schedule}
    
    print(json.dumps(output, indent=2))

if __name__ == "__main__":
    main()