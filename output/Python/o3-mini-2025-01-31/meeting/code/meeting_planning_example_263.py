#!/usr/bin/env python3
import json
from datetime import datetime, timedelta
import itertools

def parse_time(time_str):
    # time_str in format "H:MM" (24-hour)
    parts = time_str.split(':')
    return datetime(2023, 1, 1, int(parts[0]), int(parts[1]))

def format_time(dt):
    # Format time as H:MM without a leading zero for hour.
    return f"{dt.hour}:{dt.strftime('%M')}"

def add_minutes(dt, minutes):
    return dt + timedelta(minutes=minutes)

# Travel times in minutes between locations
travel_times = {
    "Bayview": {
        "Embarcadero": 19,
        "Fisherman's Wharf": 25,
        "Financial District": 19,
        "Bayview": 0
    },
    "Embarcadero": {
        "Bayview": 21,
        "Fisherman's Wharf": 6,
        "Financial District": 5,
        "Embarcadero": 0
    },
    "Fisherman's Wharf": {
        "Bayview": 26,
        "Embarcadero": 8,
        "Financial District": 11,
        "Fisherman's Wharf": 0
    },
    "Financial District": {
        "Bayview": 19,
        "Embarcadero": 4,
        "Fisherman's Wharf": 10,
        "Financial District": 0
    }
}

# Meeting constraints for each friend
# Each meeting is represented as a dictionary with:
# person, location, available_start, available_end, and min_duration (in minutes)
meetings = [
    {
        "person": "Betty",
        "location": "Embarcadero",
        "available_start": parse_time("19:45"),
        "available_end": parse_time("21:45"),
        "min_duration": 15
    },
    {
        "person": "Karen",
        "location": "Fisherman's Wharf",
        "available_start": parse_time("8:45"),
        "available_end": parse_time("15:00"),
        "min_duration": 30
    },
    {
        "person": "Anthony",
        "location": "Financial District",
        "available_start": parse_time("9:15"),
        "available_end": parse_time("21:30"),
        "min_duration": 105
    }
]

# Starting point and time
start_location = "Bayview"
start_time = parse_time("9:00")

def schedule_for_order(order):
    """
    Given an order (a tuple of meeting dicts),
    compute the itinerary with meeting start and end times.
    Returns tuple (itinerary, total_wait, final_time) if valid, otherwise None.
    """
    itinerary = []
    current_time = start_time
    current_location = start_location
    total_wait = 0

    for meeting in order:
        # Compute travel time from current location to meeting location.
        travel = travel_times[current_location][meeting["location"]]
        arrival_time = add_minutes(current_time, travel)
        # Meeting can only start when the friend is available
        meeting_start = arrival_time if arrival_time >= meeting["available_start"] else meeting["available_start"]
        # Waiting time is the delay if arrived before available_start
        wait = (meeting_start - arrival_time).total_seconds()/60
        total_wait += wait
        meeting_end = add_minutes(meeting_start, meeting["min_duration"])
        # Check if meeting end exceeds friend's available end
        if meeting_end > meeting["available_end"]:
            return None  # schedule not possible
        itinerary.append({
            "action": "meet",
            "location": meeting["location"],
            "person": meeting["person"],
            "start_time": meeting_start,
            "end_time": meeting_end
        })
        # Update current time and location
        current_time = meeting_end
        current_location = meeting["location"]
    return (itinerary, total_wait, current_time)

def select_best_schedule():
    best_schedule = None
    best_wait = None
    # Consider all permutations of the meetings (order matters)
    for perm in itertools.permutations(meetings):
        result = schedule_for_order(perm)
        if result is not None:
            itinerary, total_wait, final_time = result
            # We'll choose the schedule that finishes earliest (or minimizes waiting time)
            if best_schedule is None or final_time < best_schedule[2]:
                best_schedule = (itinerary, total_wait, final_time)
    return best_schedule

def main():
    best = select_best_schedule()
    if best is None:
        output = {"itinerary": []}
    else:
        itinerary, total_wait, final_time = best
        # Format the itinerary times as strings in H:MM (24-hour format)
        formatted_itinerary = []
        for meet in itinerary:
            formatted_itinerary.append({
                "action": meet["action"],
                "location": meet["location"],
                "person": meet["person"],
                "start_time": format_time(meet["start_time"]),
                "end_time": format_time(meet["end_time"])
            })
        output = {"itinerary": formatted_itinerary}
    print(json.dumps(output, indent=2))

if __name__ == "__main__":
    main()