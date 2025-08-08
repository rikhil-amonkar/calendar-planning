#!/usr/bin/env python3
import itertools
import json

def convert_minutes_to_time_str(minutes):
    hour = minutes // 60
    minute = minutes % 60
    return f"{hour}:{minute:02d}"

def simulate_schedule(meetings, start_time, start_location, travel_times):
    schedule = []
    current_time = start_time
    current_location = start_location
    for friend in meetings:
        # Look up the travel time from current location to friend's meeting location
        if current_location not in travel_times or friend["location"] not in travel_times[current_location]:
            return None  # no route available, not feasible
        travel_time = travel_times[current_location][friend["location"]]
        arrival_time = current_time + travel_time
        # The meeting can only start when the friend is available and you have already arrived.
        meeting_start = max(arrival_time, friend["start"])
        meeting_end = meeting_start + friend["duration"]
        # Check if the meeting can finish before the friend leaves.
        if meeting_end > friend["end"]:
            return None  # this meeting cannot be scheduled in time
        schedule.append({
            "action": "meet",
            "location": friend["location"],
            "person": friend["name"],
            "start_time": meeting_start,
            "end_time": meeting_end
        })
        # Update current time and location for the next meeting.
        current_time = meeting_end
        current_location = friend["location"]
    return schedule, current_time

def main():
    # Define the travel times (in minutes) between locations.
    travel_times = {
        "North Beach": {
            "Pacific Heights": 8,
            "Chinatown": 6,
            "Union Square": 7,
            "Mission District": 18,
            "Golden Gate Park": 22,
            "Nob Hill": 7
        },
        "Pacific Heights": {
            "North Beach": 9,
            "Chinatown": 11,
            "Union Square": 12,
            "Mission District": 15,
            "Golden Gate Park": 15,
            "Nob Hill": 8
        },
        "Chinatown": {
            "North Beach": 3,
            "Pacific Heights": 10,
            "Union Square": 7,
            "Mission District": 18,
            "Golden Gate Park": 23,
            "Nob Hill": 8
        },
        "Union Square": {
            "North Beach": 10,
            "Pacific Heights": 15,
            "Chinatown": 7,
            "Mission District": 14,
            "Golden Gate Park": 22,
            "Nob Hill": 9
        },
        "Mission District": {
            "North Beach": 17,
            "Pacific Heights": 16,
            "Chinatown": 16,
            "Union Square": 15,
            "Golden Gate Park": 17,
            "Nob Hill": 12
        },
        "Golden Gate Park": {
            "North Beach": 24,
            "Pacific Heights": 16,
            "Chinatown": 23,
            "Union Square": 22,
            "Mission District": 17,
            "Nob Hill": 20
        },
        "Nob Hill": {
            "North Beach": 8,
            "Pacific Heights": 8,
            "Chinatown": 6,
            "Union Square": 7,
            "Mission District": 13,
            "Golden Gate Park": 17
        }
    }
    
    # Define the meeting constraints.
    # Times are represented as minutes from midnight.
    # 9:00 AM = 540 minutes, 9:30 AM = 570, etc.
    friends = [
        {"name": "James", "location": "Pacific Heights", "start": 1200, "end": 1320, "duration": 120},  # 20:00-22:00
        {"name": "Robert", "location": "Chinatown", "start": 735, "end": 1005, "duration": 90},         # 12:15-16:45
        {"name": "Jeffrey", "location": "Union Square", "start": 570, "end": 930, "duration": 120},       # 9:30-15:30
        {"name": "Carol", "location": "Mission District", "start": 1095, "end": 1275, "duration": 15},    # 18:15-21:15
        {"name": "Mark", "location": "Golden Gate Park", "start": 690, "end": 1065, "duration": 15},      # 11:30-17:45
        {"name": "Sandra", "location": "Nob Hill", "start": 480, "end": 930, "duration": 15}              # 8:00-15:30
    ]
    
    # We start our day at North Beach at 9:00 AM (540 minutes).
    start_time = 540
    start_location = "North Beach"
    
    best_schedule = None
    best_meetings_count = 0
    best_finish_time = None

    # Try all possible orders of meeting friends to maximize the number of meetings.
    for perm in itertools.permutations(friends):
        result = simulate_schedule(perm, start_time, start_location, travel_times)
        if result is not None:
            schedule, finish_time = result
            meetings_count = len(schedule)
            # We choose the schedule with the maximum number of meetings;
            # if multiple schedules have the same count, choose the one finishing earlier.
            if meetings_count > best_meetings_count or (meetings_count == best_meetings_count and (best_finish_time is None or finish_time < best_finish_time)):
                best_schedule = schedule
                best_meetings_count = meetings_count
                best_finish_time = finish_time

    # Convert the meeting times from minutes to 24-hour formatted strings.
    itinerary = []
    if best_schedule is not None:
        for event in best_schedule:
            itinerary.append({
                "action": event["action"],
                "location": event["location"],
                "person": event["person"],
                "start_time": convert_minutes_to_time_str(event["start_time"]),
                "end_time": convert_minutes_to_time_str(event["end_time"])
            })
    
    output = {"itinerary": itinerary}
    print(json.dumps(output, indent=2))

if __name__ == "__main__":
    main()