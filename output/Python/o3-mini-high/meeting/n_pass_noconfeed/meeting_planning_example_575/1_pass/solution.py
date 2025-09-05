import json
import itertools

def min_to_time(minutes):
    hour = minutes // 60
    minute = minutes % 60
    return f"{hour}:{minute:02d}"

def simulate_schedule(order, travel_times):
    # Start at The Castro at 9:00 (540 minutes)
    current_time = 540  
    current_location = "The Castro"
    itinerary = []
    for meeting in order:
        key = (current_location, meeting["location"])
        if key not in travel_times:
            return None
        travel = travel_times[key]
        arrival = current_time + travel
        # The meeting can only start when both you have arrived and the person is available.
        start_meet = max(arrival, meeting["avail_start"])
        finish_meet = start_meet + meeting["duration"]
        if finish_meet > meeting["avail_end"]:
            return None  # Cannot meet this friend respecting the constraint.
        itinerary.append({
            "action": "meet",
            "location": meeting["location"],
            "person": meeting["person"],
            "start_time": min_to_time(start_meet),
            "end_time": min_to_time(finish_meet)
        })
        current_time = finish_meet
        current_location = meeting["location"]
    return itinerary, current_time

def main():
    # Define travel times in minutes between locations.
    travel_times = {
        ("The Castro", "Presidio"): 20,
        ("The Castro", "Sunset District"): 17,
        ("The Castro", "Haight-Ashbury"): 6,
        ("The Castro", "Mission District"): 7,
        ("The Castro", "Golden Gate Park"): 11,
        ("The Castro", "Russian Hill"): 18,
        ("Presidio", "The Castro"): 21,
        ("Presidio", "Sunset District"): 15,
        ("Presidio", "Haight-Ashbury"): 15,
        ("Presidio", "Mission District"): 26,
        ("Presidio", "Golden Gate Park"): 12,
        ("Presidio", "Russian Hill"): 14,
        ("Sunset District", "The Castro"): 17,
        ("Sunset District", "Presidio"): 16,
        ("Sunset District", "Haight-Ashbury"): 15,
        ("Sunset District", "Mission District"): 24,
        ("Sunset District", "Golden Gate Park"): 11,
        ("Sunset District", "Russian Hill"): 24,
        ("Haight-Ashbury", "The Castro"): 6,
        ("Haight-Ashbury", "Presidio"): 15,
        ("Haight-Ashbury", "Sunset District"): 15,
        ("Haight-Ashbury", "Mission District"): 11,
        ("Haight-Ashbury", "Golden Gate Park"): 7,
        ("Haight-Ashbury", "Russian Hill"): 17,
        ("Mission District", "The Castro"): 7,
        ("Mission District", "Presidio"): 25,
        ("Mission District", "Sunset District"): 24,
        ("Mission District", "Haight-Ashbury"): 12,
        ("Mission District", "Golden Gate Park"): 17,
        ("Mission District", "Russian Hill"): 15,
        ("Golden Gate Park", "The Castro"): 13,
        ("Golden Gate Park", "Presidio"): 11,
        ("Golden Gate Park", "Sunset District"): 10,
        ("Golden Gate Park", "Haight-Ashbury"): 7,
        ("Golden Gate Park", "Mission District"): 17,
        ("Golden Gate Park", "Russian Hill"): 19,
        ("Russian Hill", "The Castro"): 21,
        ("Russian Hill", "Presidio"): 14,
        ("Russian Hill", "Sunset District"): 23,
        ("Russian Hill", "Haight-Ashbury"): 17,
        ("Russian Hill", "Mission District"): 16,
        ("Russian Hill", "Golden Gate Park"): 21,
    }

    # Define the meeting constraints.
    # Times are converted to minutes after midnight.
    meetings = [
        {
            "person": "Rebecca",
            "location": "Presidio",
            "avail_start": 18 * 60 + 15,  # 18:15 -> 1095
            "avail_end": 20 * 60 + 45,    # 20:45 -> 1245
            "duration": 60
        },
        {
            "person": "Linda",
            "location": "Sunset District",
            "avail_start": 15 * 60 + 30,  # 15:30 -> 930
            "avail_end": 19 * 60 + 45,    # 19:45 -> 1185
            "duration": 30
        },
        {
            "person": "Elizabeth",
            "location": "Haight-Ashbury",
            "avail_start": 17 * 60 + 15,  # 17:15 -> 1035
            "avail_end": 19 * 60 + 30,    # 19:30 -> 1170
            "duration": 105
        },
        {
            "person": "William",
            "location": "Mission District",
            "avail_start": 13 * 60 + 15,  # 13:15 -> 795
            "avail_end": 19 * 60 + 30,    # 19:30 -> 1170
            "duration": 30
        },
        {
            "person": "Robert",
            "location": "Golden Gate Park",
            "avail_start": 14 * 60 + 15,  # 14:15 -> 855
            "avail_end": 21 * 60 + 30,    # 21:30 -> 1290
            "duration": 45
        },
        {
            "person": "Mark",
            "location": "Russian Hill",
            "avail_start": 10 * 60,       # 10:00 -> 600
            "avail_end": 21 * 60 + 15,    # 21:15 -> 1275
            "duration": 75
        }
    ]

    best_itinerary = None
    best_finish_time = float("inf")
    # We want to maximize the number of meetings (i.e. meet as many friends as possible).
    # Here we search for an ordering that fits all meetings; if multiple, choose the one finishing earliest.
    for order in itertools.permutations(meetings):
        result = simulate_schedule(order, travel_times)
        if result is not None:
            itinerary, finish_time = result
            if finish_time < best_finish_time:
                best_finish_time = finish_time
                best_itinerary = itinerary

    output = {"itinerary": best_itinerary if best_itinerary is not None else []}
    print(json.dumps(output, indent=2))

if __name__ == "__main__":
    main()