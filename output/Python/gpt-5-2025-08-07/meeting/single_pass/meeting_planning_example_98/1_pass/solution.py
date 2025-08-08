import json
from typing import List, Tuple, Dict, Any

# Utility functions for time handling
def parse_time(t: str) -> int:
    # 'H:MM' -> minutes from midnight
    h, m = t.split(":")
    return int(h) * 60 + int(m)

def fmt_time(minutes: int) -> str:
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

# Travel time lookup with default 0 if same location
def get_travel_time(travel_map: Dict[Tuple[str, str], int], a: str, b: str) -> int:
    if a == b:
        return 0
    return travel_map.get((a, b), float('inf'))

# Inputs (as variables as required)
start_location = "Alamo Square"
start_time_str = "9:00"

travel_times_minutes = {
    ("Alamo Square", "Richmond District"): 12,
    ("Richmond District", "Alamo Square"): 13,
}

friends = [
    {
        "name": "Timothy",
        "location": "Richmond District",
        "window_start": "20:45",
        "window_end": "21:30",
        "min_duration": 45,  # minutes
    }
]

# Convert and normalize inputs
start_time = parse_time(start_time_str)
for f in friends:
    f["win_start_min"] = parse_time(f["window_start"])
    f["win_end_min"] = parse_time(f["window_end"])

# Backtracking search to consider different schedules and choose the optimal
def search(current_loc: str, current_time: int, remaining: List[Dict[str, Any]]) -> Tuple[List[Dict[str, Any]], int, int]:
    # Returns (itinerary, meetings_count, end_time)
    best_itinerary: List[Dict[str, Any]] = []
    best_count = 0
    best_end_time = current_time  # for tie-breaking: earlier finish is better

    # Option: stop now, no more meetings
    best_tuple = (best_itinerary, best_count, best_end_time)

    for i, friend in enumerate(remaining):
        travel = get_travel_time(travel_times_minutes, current_loc, friend["location"])
        if travel == float('inf'):
            continue  # unreachable path

        earliest_arrival = current_time + travel
        # Meeting must start within friend window after arrival
        meeting_start = max(earliest_arrival, friend["win_start_min"])
        meeting_end = meeting_start + friend["min_duration"]

        # Must finish before or at end of availability
        if meeting_end <= friend["win_end_min"]:
            event = {
                "action": "meet",
                "location": friend["location"],
                "person": friend["name"],
                "start_time": fmt_time(meeting_start),
                "end_time": fmt_time(meeting_end),
            }
            # Recurse with friend removed from remaining
            next_remaining = remaining[:i] + remaining[i+1:]
            sub_itinerary, sub_count, sub_end_time = search(friend["location"], meeting_end, next_remaining)

            candidate_itinerary = [event] + sub_itinerary
            candidate_count = 1 + sub_count
            candidate_end_time = sub_end_time

            # Choose best: maximize count, then minimize end time, then earliest first meeting start
            if candidate_count > best_tuple[1]:
                best_tuple = (candidate_itinerary, candidate_count, candidate_end_time)
            elif candidate_count == best_tuple[1]:
                # earlier finish is better
                if candidate_end_time < best_tuple[2]:
                    best_tuple = (candidate_itinerary, candidate_count, candidate_end_time)
                elif candidate_end_time == best_tuple[2]:
                    # earlier first meeting start is better
                    if candidate_itinerary and best_tuple[0]:
                        cand_first_start = parse_time(candidate_itinerary[0]["start_time"])
                        best_first_start = parse_time(best_tuple[0][0]["start_time"])
                        if cand_first_start < best_first_start:
                            best_tuple = (candidate_itinerary, candidate_count, candidate_end_time)
                    elif candidate_itinerary and not best_tuple[0]:
                        best_tuple = (candidate_itinerary, candidate_count, candidate_end_time)

    return best_tuple

# Run search to compute optimal plan
itinerary, _, _ = search(start_location, start_time, friends)

# Output as JSON-formatted dictionary
result = {
    "itinerary": itinerary
}

print(json.dumps(result, ensure_ascii=False))