#!/usr/bin/env python3
import itertools
import json

# Helper function: convert minutes (since midnight) to H:MM string (no leading zero for hour)
def minutes_to_timestr(minutes):
    hour = minutes // 60
    minute = minutes % 60
    return f"{hour}:{minute:02d}"

# Define travel times (in minutes) between locations
# The keys are tuples (source, destination)
travel_times = {
    ("The Castro", "Bayview"): 19,
    ("The Castro", "Pacific Heights"): 16,
    ("The Castro", "Alamo Square"): 8,
    ("The Castro", "Fisherman's Wharf"): 24,
    ("The Castro", "Golden Gate Park"): 11,

    ("Bayview", "The Castro"): 20,
    ("Bayview", "Pacific Heights"): 23,
    ("Bayview", "Alamo Square"): 16,
    ("Bayview", "Fisherman's Wharf"): 25,
    ("Bayview", "Golden Gate Park"): 22,

    ("Pacific Heights", "The Castro"): 16,
    ("Pacific Heights", "Bayview"): 22,
    ("Pacific Heights", "Alamo Square"): 10,
    ("Pacific Heights", "Fisherman's Wharf"): 13,
    ("Pacific Heights", "Golden Gate Park"): 15,

    ("Alamo Square", "The Castro"): 8,
    ("Alamo Square", "Bayview"): 16,
    ("Alamo Square", "Pacific Heights"): 10,
    ("Alamo Square", "Fisherman's Wharf"): 19,
    ("Alamo Square", "Golden Gate Park"): 9,

    ("Fisherman's Wharf", "The Castro"): 26,
    ("Fisherman's Wharf", "Bayview"): 26,
    ("Fisherman's Wharf", "Pacific Heights"): 12,
    ("Fisherman's Wharf", "Alamo Square"): 20,
    ("Fisherman's Wharf", "Golden Gate Park"): 25,

    ("Golden Gate Park", "The Castro"): 13,
    ("Golden Gate Park", "Bayview"): 23,
    ("Golden Gate Park", "Pacific Heights"): 16,
    ("Golden Gate Park", "Alamo Square"): 10,
    ("Golden Gate Park", "Fisherman's Wharf"): 24,
}

# Define the meeting constraints for each friend.
# Times are stored as minutes since midnight.
meetings = {
    "Rebecca": {
        "location": "Bayview",
        "available_start": 9 * 60,        # 9:00
        "available_end": 12 * 60 + 45,      # 12:45
        "min_duration": 90
    },
    "Amanda": {
        "location": "Pacific Heights",
        "available_start": 18 * 60 + 30,    # 18:30
        "available_end": 21 * 60 + 45,      # 21:45
        "min_duration": 90
    },
    "James": {
        "location": "Alamo Square",
        "available_start": 9 * 60 + 45,     # 9:45
        "available_end": 21 * 60 + 15,      # 21:15
        "min_duration": 90
    },
    "Sarah": {
        "location": "Fisherman's Wharf",
        "available_start": 8 * 60,          # 8:00
        "available_end": 21 * 60 + 30,      # 21:30
        "min_duration": 90
    },
    "Melissa": {
        "location": "Golden Gate Park",
        "available_start": 9 * 60,          # 9:00
        "available_end": 18 * 60 + 45,      # 18:45
        "min_duration": 90
    }
}

# Starting parameters
start_location = "The Castro"
start_time = 9 * 60  # 9:00 AM in minutes since midnight

# This function simulates a given order of meetings and returns the itinerary if valid, else None.
def simulate_order(order):
    itinerary = []
    current_time = start_time
    current_location = start_location

    for person in order:
        details = meetings[person]
        meeting_location = details["location"]

        # Get travel time from current_location to meeting_location
        if (current_location, meeting_location) not in travel_times:
            return None  # no route defined
        travel_time = travel_times[(current_location, meeting_location)]
        arrival_time = current_time + travel_time

        # Wait until the person's availability start if arrived early
        meeting_start = max(arrival_time, details["available_start"])
        meeting_end = meeting_start + details["min_duration"]

        # Check if meeting can be done within available window
        if meeting_end > details["available_end"]:
            return None

        # Append meeting to itinerary
        itinerary.append({
            "action": "meet",
            "location": meeting_location,
            "person": person,
            "start_time": minutes_to_timestr(meeting_start),
            "end_time": minutes_to_timestr(meeting_end)
        })

        # Update current time and location for next meeting
        current_time = meeting_end
        current_location = meeting_location

    return itinerary

def main():
    persons = list(meetings.keys())
    best_itinerary = None
    best_count = 0

    # Try all permutations of meeting orders
    for order in itertools.permutations(persons):
        itinerary = simulate_order(order)
        if itinerary is not None:
            count = len(itinerary)
            if count > best_count:
                best_count = count
                best_itinerary = itinerary
            # Since our goal is to meet as many as possible and maximum is 5,
            # we can break early if we found all 5 meetings.
            if best_count == len(persons):
                break

    # Prepare the output dictionary
    output = {"itinerary": []}
    if best_itinerary is not None:
        output["itinerary"] = best_itinerary
    else:
        output["itinerary"] = []  # no valid schedule found

    # Print the JSON-formatted output.
    print(json.dumps(output, indent=2))

if __name__ == '__main__':
    main()