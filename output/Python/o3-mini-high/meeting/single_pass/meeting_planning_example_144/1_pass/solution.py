#!/usr/bin/env python3
import json
import itertools

def minutes_to_time(m):
    hour = m // 60
    minute = m % 60
    return f"{hour}:{minute:02d}"

def compute_schedule(order, start_location, start_time, travel_times, friend_data):
    schedule = []
    current_time = start_time
    current_location = start_location
    for friend in order:
        friend_info = friend_data[friend]
        destination = friend_info["location"]
        travel_time = travel_times[current_location][destination]
        arrival_time = current_time + travel_time
        meeting_start = max(arrival_time, friend_info["available_start"])
        meeting_end = meeting_start + friend_info["min_duration"]
        # Check if the meeting can finish before the friend leaves.
        if meeting_end > friend_info["available_end"]:
            return None  # This schedule is not feasible.
        event = {
            "action": "meet",
            "location": destination,
            "person": friend,
            "start_time": minutes_to_time(meeting_start),
            "end_time": minutes_to_time(meeting_end)
        }
        schedule.append(event)
        current_time = meeting_end
        current_location = destination
    return schedule, current_time

def main():
    # Starting point and time at The Castro.
    start_location = "The Castro"
    start_time = 9 * 60  # 9:00 AM in minutes

    # Define travel times between locations (in minutes).
    travel_times = {
        "The Castro": {"Mission District": 7, "Financial District": 20},
        "Mission District": {"The Castro": 7, "Financial District": 17},
        "Financial District": {"The Castro": 23, "Mission District": 17}
    }
    
    # Friend meeting constraints.
    # Times are stored as minutes from midnight.
    friend_data = {
        "Laura": {
            "location": "Mission District",
            "available_start": 12 * 60 + 15,  # 12:15 PM -> 735 minutes
            "available_end": 19 * 60 + 45,    # 7:45 PM -> 1185 minutes
            "min_duration": 75
        },
        "Anthony": {
            "location": "Financial District",
            "available_start": 12 * 60 + 30,  # 12:30 PM -> 750 minutes
            "available_end": 14 * 60 + 45,    # 2:45 PM -> 885 minutes
            "min_duration": 30
        }
    }
    
    # Try all possible orders of meeting friends.
    friends = list(friend_data.keys())  # ["Laura", "Anthony"]
    best_schedule = None
    best_finish_time = float('inf')
    
    for order in itertools.permutations(friends):
        result = compute_schedule(order, start_location, start_time, travel_times, friend_data)
        if result is not None:
            schedule, finish_time = result
            # Optimize by selecting the schedule that finishes earliest.
            if finish_time < best_finish_time:
                best_finish_time = finish_time
                best_schedule = schedule

    # Prepare the output JSON structure.
    output = {"itinerary": best_schedule if best_schedule is not None else []}
    print(json.dumps(output))

if __name__ == "__main__":
    main()