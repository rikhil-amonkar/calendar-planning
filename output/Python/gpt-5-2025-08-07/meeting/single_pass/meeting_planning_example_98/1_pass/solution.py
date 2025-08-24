import json
from typing import List, Dict, Tuple, Optional

# Input variables
arrival_location = "Alamo Square"
arrival_time_str = "9:00"

travel_times = {
    ("Alamo Square", "Richmond District"): 12,
    ("Richmond District", "Alamo Square"): 13
}

friends = [
    {
        "name": "Timothy",
        "location": "Richmond District",
        "start": "20:45",
        "end": "21:30"
    }
]

min_meeting_duration = 45  # minutes


# Utility functions
def parse_time(t: str) -> int:
    h, m = map(int, t.split(":"))
    return h * 60 + m


def format_time(minutes: int) -> str:
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"


def get_travel_time(a: str, b: str) -> Optional[int]:
    if a == b:
        return 0
    return travel_times.get((a, b), None)


# Generate candidate meeting intervals for each friend (independent of travel).
def generate_candidate_intervals(friend: Dict, min_dur: int) -> List[Tuple[int, int]]:
    start = parse_time(friend["start"])
    end = parse_time(friend["end"])
    latest_start = end - min_dur
    if latest_start < start:
        return []
    # Consider all possible minute-by-minute starts within availability
    candidates = []
    for s in range(start, latest_start + 1):
        candidates.append((s, s + min_dur))
    return candidates


# Depth-first search to construct optimal itinerary (max # of meetings)
def search_optimal_itinerary(
    current_location: str,
    current_time: int,
    remaining_friends: List[Dict],
    candidate_windows: Dict[str, List[Tuple[int, int]]],
) -> List[Dict]:
    best_schedule: List[Dict] = []

    # Try scheduling each remaining friend next
    for i, friend in enumerate(remaining_friends):
        loc = friend["location"]
        # Compute travel time from current location to friend's location
        ttime = get_travel_time(current_location, loc)
        if ttime is None:
            continue  # cannot travel, skip

        # Try each candidate window for this friend that is feasible given travel time
        feasible_windows = []
        for (s, e) in candidate_windows[friend["name"]]:
            # Must arrive by s
            arrival_needed = s
            earliest_arrival = current_time + ttime
            if earliest_arrival <= arrival_needed:
                feasible_windows.append((s, e))

        # Among feasible windows, try them in a deterministic order (earliest start first)
        for (s, e) in feasible_windows:
            meeting = {
                "action": "meet",
                "location": loc,
                "person": friend["name"],
                "start_time": format_time(s),
                "end_time": format_time(e),
            }
            # Recurse with updated state
            next_friends = remaining_friends[:i] + remaining_friends[i+1:]
            rest_schedule = search_optimal_itinerary(
                loc, e, next_friends, candidate_windows
            )
            schedule = [meeting] + rest_schedule

            # Choose the schedule that meets the most friends; tie-breaker: earliest final end time
            if len(schedule) > len(best_schedule):
                best_schedule = schedule
            elif len(schedule) == len(best_schedule):
                if schedule:
                    end_time_schedule = parse_time(schedule[-1]["end_time"])
                    end_time_best = parse_time(best_schedule[-1]["end_time"]) if best_schedule else float("inf")
                    if end_time_schedule < end_time_best:
                        best_schedule = schedule

    return best_schedule


def compute_itinerary() -> List[Dict]:
    # Precompute candidate windows for each friend
    candidate_windows = {}
    for f in friends:
        candidate_windows[f["name"]] = generate_candidate_intervals(f, min_meeting_duration)

    # Start search from arrival location/time
    start_time = parse_time(arrival_time_str)
    itinerary = search_optimal_itinerary(arrival_location, start_time, friends, candidate_windows)

    # Additional feasibility check: ensure the first scheduled meeting is reachable from arrival
    if itinerary:
        first = itinerary[0]
        ttime = get_travel_time(arrival_location, first["location"])
        if ttime is None:
            return []
        if parse_time(first["start_time"]) < (start_time + ttime):
            # Not actually reachable; discard
            return []

    return itinerary


def main():
    itinerary = compute_itinerary()
    output = {"itinerary": itinerary}
    print(json.dumps(output))


if __name__ == "__main__":
    main()