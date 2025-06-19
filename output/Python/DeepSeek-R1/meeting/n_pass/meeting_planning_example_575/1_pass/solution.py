import itertools
import json

def main():
    # Build travel time dictionary
    travel_times = {
        "The Castro": {
            "Presidio": 20,
            "Sunset District": 17,
            "Haight-Ashbury": 6,
            "Mission District": 7,
            "Golden Gate Park": 11,
            "Russian Hill": 18
        },
        "Presidio": {
            "The Castro": 21,
            "Sunset District": 15,
            "Haight-Ashbury": 15,
            "Mission District": 26,
            "Golden Gate Park": 12,
            "Russian Hill": 14
        },
        "Sunset District": {
            "The Castro": 17,
            "Presidio": 16,
            "Haight-Ashbury": 15,
            "Mission District": 24,
            "Golden Gate Park": 11,
            "Russian Hill": 24
        },
        "Haight-Ashbury": {
            "The Castro": 6,
            "Presidio": 15,
            "Sunset District": 15,
            "Mission District": 11,
            "Golden Gate Park": 7,
            "Russian Hill": 17
        },
        "Mission District": {
            "The Castro": 7,
            "Presidio": 25,
            "Sunset District": 24,
            "Haight-Ashbury": 12,
            "Golden Gate Park": 17,
            "Russian Hill": 15
        },
        "Golden Gate Park": {
            "The Castro": 13,
            "Presidio": 11,
            "Sunset District": 10,
            "Haight-Ashbury": 7,
            "Mission District": 17,
            "Russian Hill": 19
        },
        "Russian Hill": {
            "The Castro": 21,
            "Presidio": 14,
            "Sunset District": 23,
            "Haight-Ashbury": 17,
            "Mission District": 16,
            "Golden Gate Park": 21
        }
    }

    # Define friends with their constraints (times in minutes)
    friends = [
        {"name": "Rebecca", "location": "Presidio", "start": 18*60+15, "end": 20*60+45, "min_duration": 60},
        {"name": "Linda", "location": "Sunset District", "start": 15*60+30, "end": 19*60+45, "min_duration": 30},
        {"name": "Elizabeth", "location": "Haight-Ashbury", "start": 17*60+15, "end": 19*60+30, "min_duration": 105},
        {"name": "William", "location": "Mission District", "start": 13*60+15, "end": 19*60+30, "min_duration": 30},
        {"name": "Robert", "location": "Golden Gate Park", "start": 14*60+15, "end": 21*60+30, "min_duration": 45},
        {"name": "Mark", "location": "Russian Hill", "start": 10*60+00, "end": 21*60+15, "min_duration": 75}
    ]

    # Convert minutes to time string (H:MM)
    def format_time(minutes):
        h = minutes // 60
        m = minutes % 60
        return f"{h}:{m:02d}"

    start_time = 9 * 60  # 9:00 AM in minutes
    start_location = "The Castro"
    best_schedule = None
    max_meetings = len(friends)

    # Try from max_meetings down to 0
    found = False
    for size in range(max_meetings, 0, -1):
        for subset in itertools.combinations(friends, size):
            for perm in itertools.permutations(subset):
                current_time = start_time
                current_location = start_location
                itinerary = []
                valid = True
                for friend in perm:
                    # Get travel time from current_location to friend's location
                    travel = travel_times[current_location][friend["location"]]
                    current_time += travel  # arrival time at friend's location

                    # Calculate meeting start and end
                    meeting_start = max(current_time, friend["start"])
                    meeting_end = meeting_start + friend["min_duration"]

                    # Check if meeting fits in the window
                    if meeting_end > friend["end"]:
                        valid = False
                        break

                    # Record this meeting
                    itinerary.append({
                        "friend": friend,
                        "start": meeting_start,
                        "end": meeting_end
                    })
                    current_time = meeting_end
                    current_location = friend["location"]

                if valid:
                    best_schedule = itinerary
                    found = True
                    break
            if found:
                break
        if found:
            break

    # If no schedule found, best_schedule remains None -> empty itinerary
    if best_schedule is None:
        result = {"itinerary": []}
    else:
        # Format the itinerary
        formatted_itinerary = []
        for meeting in best_schedule:
            friend = meeting["friend"]
            formatted_itinerary.append({
                "action": "meet",
                "location": friend["location"],
                "person": friend["name"],
                "start_time": format_time(meeting["start"]),
                "end_time": format_time(meeting["end"])
            })
        result = {"itinerary": formatted_itinerary}

    # Output as JSON
    print(json.dumps(result))

if __name__ == "__main__":
    main()