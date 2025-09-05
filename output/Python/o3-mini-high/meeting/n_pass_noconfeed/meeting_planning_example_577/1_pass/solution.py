import itertools
import json

def time_to_minutes(t):
    # Expects time string like "9:00" or "20:45"
    hours, minutes = t.split(":")
    return int(hours) * 60 + int(minutes)

def minutes_to_time(m):
    hours = m // 60
    minutes = m % 60
    return f"{hours}:{minutes:02d}"

# Define the travel time matrix (in minutes)
travel_times = {
    "Haight-Ashbury": {
        "Russian Hill": 17,
        "Fisherman's Wharf": 23,
        "Nob Hill": 15,
        "Golden Gate Park": 7,
        "Alamo Square": 5,
        "Pacific Heights": 12
    },
    "Russian Hill": {
        "Haight-Ashbury": 17,
        "Fisherman's Wharf": 7,
        "Nob Hill": 5,
        "Golden Gate Park": 21,
        "Alamo Square": 15,
        "Pacific Heights": 7
    },
    "Fisherman's Wharf": {
        "Haight-Ashbury": 22,
        "Russian Hill": 7,
        "Nob Hill": 11,
        "Golden Gate Park": 25,
        "Alamo Square": 20,
        "Pacific Heights": 12
    },
    "Nob Hill": {
        "Haight-Ashbury": 13,
        "Russian Hill": 5,
        "Fisherman's Wharf": 11,
        "Golden Gate Park": 17,
        "Alamo Square": 11,
        "Pacific Heights": 8
    },
    "Golden Gate Park": {
        "Haight-Ashbury": 7,
        "Russian Hill": 19,
        "Fisherman's Wharf": 24,
        "Nob Hill": 20,
        "Alamo Square": 10,
        "Pacific Heights": 16
    },
    "Alamo Square": {
        "Haight-Ashbury": 5,
        "Russian Hill": 13,
        "Fisherman's Wharf": 19,
        "Nob Hill": 11,
        "Golden Gate Park": 9,
        "Pacific Heights": 10
    },
    "Pacific Heights": {
        "Haight-Ashbury": 11,
        "Russian Hill": 7,
        "Fisherman's Wharf": 13,
        "Nob Hill": 8,
        "Golden Gate Park": 15,
        "Alamo Square": 10
    }
}

# Define the meeting participants and constraints.
# Each participant dictionary contains:
# - person: Name
# - location: Where they will be
# - avail_start: Availability start time (in minutes after midnight)
# - avail_end: Availability end time (in minutes after midnight)
# - meeting_duration: Minimum meeting time required (in minutes)
participants = [
    {
        "person": "Stephanie",
        "location": "Russian Hill",
        "avail_start": time_to_minutes("20:00"),
        "avail_end": time_to_minutes("20:45"),
        "meeting_duration": 15
    },
    {
        "person": "Kevin",
        "location": "Fisherman's Wharf",
        "avail_start": time_to_minutes("19:15"),
        "avail_end": time_to_minutes("21:45"),
        "meeting_duration": 75
    },
    {
        "person": "Robert",
        "location": "Nob Hill",
        "avail_start": time_to_minutes("7:45"),
        "avail_end": time_to_minutes("10:30"),
        "meeting_duration": 90
    },
    {
        "person": "Steven",
        "location": "Golden Gate Park",
        "avail_start": time_to_minutes("8:30"),
        "avail_end": time_to_minutes("17:00"),
        "meeting_duration": 75
    },
    {
        "person": "Anthony",
        "location": "Alamo Square",
        "avail_start": time_to_minutes("7:45"),
        "avail_end": time_to_minutes("19:45"),
        "meeting_duration": 15
    },
    {
        "person": "Sandra",
        "location": "Pacific Heights",
        "avail_start": time_to_minutes("14:45"),
        "avail_end": time_to_minutes("21:45"),
        "meeting_duration": 45
    }
]

# Starting point and time
start_location = "Haight-Ashbury"
start_time = time_to_minutes("9:00")  # 9:00 AM

def simulate_schedule(order):
    """
    Simulate a schedule given an order (list) of participant dictionaries.
    Returns a tuple (itinerary, finishing_time) if feasible, or None if not.
    """
    itinerary = []
    current_time = start_time
    current_location = start_location

    for friend in order:
        # Get travel time from current location to friend's location
        travel = travel_times[current_location][friend["location"]]
        arrival_time = current_time + travel
        # Meeting can only begin when friend is available
        meeting_start = max(arrival_time, friend["avail_start"])
        meeting_end = meeting_start + friend["meeting_duration"]

        # Check if meeting fits within the friend's availability window
        if meeting_end > friend["avail_end"]:
            return None

        meeting_entry = {
            "action": "meet",
            "location": friend["location"],
            "person": friend["person"],
            "start_time": minutes_to_time(meeting_start),
            "end_time": minutes_to_time(meeting_end)
        }
        itinerary.append(meeting_entry)
        # Update current time and location for next meeting
        current_time = meeting_end
        current_location = friend["location"]

    return itinerary, current_time

def find_optimal_schedule(participants):
    best_schedule = None
    best_count = 0
    best_finish = float('inf')

    n = len(participants)
    # Try schedules with maximum number of meetings downwards.
    # We want to maximize the number of friends met.
    for r in range(n, 0, -1):
        feasible_schedules = []
        # Generate all permutations of r participants out of the list.
        for order in itertools.permutations(participants, r):
            result = simulate_schedule(order)
            if result is not None:
                itinerary, finish_time = result
                feasible_schedules.append((itinerary, finish_time))
        if feasible_schedules:
            # Among those with r meetings, pick the one finishing earliest.
            best_itin, best_finish = min(feasible_schedules, key=lambda x: x[1])
            best_count = r
            best_schedule = best_itin
            break
    return best_schedule, best_count

def main():
    optimal_itinerary, count = find_optimal_schedule(participants)
    # If no feasible schedule found, output an empty itinerary.
    if optimal_itinerary is None:
        output = {"itinerary": []}
    else:
        output = {"itinerary": optimal_itinerary}
    print(json.dumps(output, indent=2))

if __name__ == '__main__':
    main()