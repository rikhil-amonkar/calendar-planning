import json
import itertools

# Helper functions to convert between minutes and "H:MM" string format.
def minutes_to_str(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

# Travel time data (in minutes) between locations.
travel_times = {
    "Marina District": {
        "Mission District": 20,
        "Fisherman's Wharf": 10,
        "Presidio": 10,
        "Union Square": 16,
        "Sunset District": 19,
        "Financial District": 17,
        "Haight-Ashbury": 16,
        "Russian Hill": 8
    },
    "Mission District": {
        "Marina District": 19,
        "Fisherman's Wharf": 22,
        "Presidio": 25,
        "Union Square": 15,
        "Sunset District": 24,
        "Financial District": 15,
        "Haight-Ashbury": 12,
        "Russian Hill": 15
    },
    "Fisherman's Wharf": {
        "Marina District": 9,
        "Mission District": 22,
        "Presidio": 17,
        "Union Square": 13,
        "Sunset District": 27,
        "Financial District": 11,
        "Haight-Ashbury": 22,
        "Russian Hill": 7
    },
    "Presidio": {
        "Marina District": 11,
        "Mission District": 26,
        "Fisherman's Wharf": 19,
        "Union Square": 22,
        "Sunset District": 15,
        "Financial District": 23,
        "Haight-Ashbury": 15,
        "Russian Hill": 14
    },
    "Union Square": {
        "Marina District": 18,
        "Mission District": 14,
        "Fisherman's Wharf": 15,
        "Presidio": 24,
        "Sunset District": 27,
        "Financial District": 9,
        "Haight-Ashbury": 18,
        "Russian Hill": 13
    },
    "Sunset District": {
        "Marina District": 21,
        "Mission District": 25,
        "Fisherman's Wharf": 29,
        "Presidio": 16,
        "Union Square": 30,
        "Financial District": 30,
        "Haight-Ashbury": 15,
        "Russian Hill": 24
    },
    "Financial District": {
        "Marina District": 15,
        "Mission District": 17,
        "Fisherman's Wharf": 10,
        "Presidio": 22,
        "Union Square": 9,
        "Sunset District": 30,
        "Haight-Ashbury": 19,
        "Russian Hill": 11
    },
    "Haight-Ashbury": {
        "Marina District": 17,
        "Mission District": 11,
        "Fisherman's Wharf": 23,
        "Presidio": 15,
        "Union Square": 19,
        "Sunset District": 15,
        "Financial District": 21,
        "Russian Hill": 17
    },
    "Russian Hill": {
        "Marina District": 7,
        "Mission District": 16,
        "Fisherman's Wharf": 7,
        "Presidio": 14,
        "Union Square": 10,
        "Sunset District": 23,
        "Financial District": 11,
        "Haight-Ashbury": 17
    }
}

# Meeting constraints.
# Each meeting has a person, the district where the meeting is held, their available window (in minutes after midnight)
# and the minimum required meeting duration (in minutes).
meetings = [
    {"person": "Karen", "location": "Mission District", "avail_start": 14 * 60 + 15, "avail_end": 22 * 60, "duration": 30},
    {"person": "Richard", "location": "Fisherman's Wharf", "avail_start": 14 * 60 + 30, "avail_end": 17 * 60 + 30, "duration": 30},
    {"person": "Robert", "location": "Presidio", "avail_start": 21 * 60 + 45, "avail_end": 22 * 60 + 45, "duration": 60},
    {"person": "Joseph", "location": "Union Square", "avail_start": 11 * 60 + 45, "avail_end": 14 * 60 + 45, "duration": 120},
    {"person": "Helen", "location": "Sunset District", "avail_start": 14 * 60 + 45, "avail_end": 20 * 60 + 45, "duration": 105},
    {"person": "Elizabeth", "location": "Financial District", "avail_start": 10 * 60, "avail_end": 12 * 60 + 45, "duration": 75},
    {"person": "Kimberly", "location": "Haight-Ashbury", "avail_start": 14 * 60 + 15, "avail_end": 17 * 60 + 30, "duration": 105},
    {"person": "Ashley", "location": "Russian Hill", "avail_start": 11 * 60 + 30, "avail_end": 21 * 60 + 30, "duration": 45}
]

START_TIME = 9 * 60  # 9:00 AM in minutes
START_LOCATION = "Marina District"

def simulate_schedule(order):
    """Given an order (list) of meetings, simulate the day and return the itinerary if feasible.
       Otherwise, return None.
    """
    current_time = START_TIME
    current_location = START_LOCATION
    itinerary = []
    
    for meeting in order:
        # Get travel time from current location to meeting location.
        travel = travel_times[current_location][meeting["location"]]
        arrival_time = current_time + travel
        # Meeting cannot start before the person's available start.
        meeting_start = max(arrival_time, meeting["avail_start"])
        meeting_end = meeting_start + meeting["duration"]
        # Check if meeting can finish before the person's available end.
        if meeting_end > meeting["avail_end"]:
            return None  # This ordering is not feasible.
        # Add meeting to itinerary.
        itinerary.append({
            "action": "meet",
            "location": meeting["location"],
            "person": meeting["person"],
            "start_time": minutes_to_str(meeting_start),
            "end_time": minutes_to_str(meeting_end)
        })
        # Update current time and location.
        current_time = meeting_end
        current_location = meeting["location"]
    return itinerary, current_time

def find_optimal_schedule(meetings):
    best_itinerary = None
    best_meetings_count = 0
    best_end_time = float('inf')
    
    # Try all permutations of meetings.
    for order in itertools.permutations(meetings):
        result = simulate_schedule(order)
        if result is None:
            continue
        itinerary, end_time = result
        count = len(itinerary)
        # We want to maximize the number of meetings.
        if count > best_meetings_count or (count == best_meetings_count and end_time < best_end_time):
            best_meetings_count = count
            best_end_time = end_time
            best_itinerary = itinerary
            # Early exit if we scheduled all meetings.
            if best_meetings_count == len(meetings):
                # Since all meetings are met, we can break early.
                # Comment out the break if you want to check for a schedule with lower end time.
                pass  
    return best_itinerary

if __name__ == "__main__":
    optimal_itinerary = find_optimal_schedule(meetings)
    result = {"itinerary": optimal_itinerary if optimal_itinerary is not None else []}
    print(json.dumps(result))