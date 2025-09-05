import json
from typing import List, Dict, Tuple

# SOLUTION:

def parse_time(t: str) -> int:
    """Convert 'H:MM' (24h) to minutes since midnight."""
    h, m = map(int, t.split(":"))
    return h * 60 + m

def time_to_str(minutes: int) -> str:
    """Convert minutes since midnight to 'H:MM' with no leading zero on hour."""
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

def get_travel_time(travel_map: Dict[Tuple[str, str], int], a: str, b: str) -> int:
    if a == b:
        return 0
    if (a, b) in travel_map:
        return travel_map[(a, b)]
    raise ValueError(f"No travel time specified between {a} and {b}")

def evaluate_schedule(itinerary: List[Dict]) -> Tuple[int, int]:
    """Return (friends_met_count, total_meeting_minutes)."""
    friends = {item["person"] for item in itinerary}
    total_minutes = sum(
        parse_time(item["end_time"]) - parse_time(item["start_time"]) for item in itinerary
    )
    return len(friends), total_minutes

def plan_schedule(
    start_location: str,
    start_time_str: str,
    travel_map: Dict[Tuple[str, str], int],
    friends: List[Dict],
) -> List[Dict]:
    start_time = parse_time(start_time_str)

    # Preprocess friends into a uniform structure
    friend_list = []
    for f in friends:
        friend_list.append({
            "name": f["name"],
            "location": f["location"],
            "start": parse_time(f["start"]),
            "end": parse_time(f["end"]),
            "min_meet": f["min_meet"]
        })

    n = len(friend_list)
    best_itinerary: List[Dict] = []

    # Backtracking search over possible schedules
    def backtrack(current_loc: str, current_time: int, met_mask: int, itinerary: List[Dict]):
        nonlocal best_itinerary

        # Update best by objective: maximize friends met, then total minutes
        best_friends, best_minutes = evaluate_schedule(best_itinerary)
        this_friends, this_minutes = evaluate_schedule(itinerary)
        if (this_friends > best_friends) or (this_friends == best_friends and this_minutes > best_minutes):
            best_itinerary = list(itinerary)

        # Try to meet remaining friends
        for i, fr in enumerate(friend_list):
            if (met_mask >> i) & 1:
                continue  # already met

            # Compute earliest feasible start time
            travel_minutes = get_travel_time(travel_map, current_loc, fr["location"])
            arrival_time = current_time + travel_minutes
            earliest_start = max(arrival_time, fr["start"])

            # Check feasibility with min meeting requirement
            if earliest_start + fr["min_meet"] > fr["end"]:
                continue  # cannot meet minimum duration

            # Consider various meeting durations: min, max, and stepped durations
            max_duration = fr["end"] - earliest_start
            durations = set()
            durations.add(fr["min_meet"])
            durations.add(max_duration)
            # Add a few stepped options to consider different schedules
            step = 30  # minutes
            d = fr["min_meet"]
            while d < max_duration:
                durations.add(d)
                d += step

            for dur in sorted(durations):
                if dur < fr["min_meet"] or earliest_start + dur > fr["end"]:
                    continue
                meet_start = earliest_start
                meet_end = earliest_start + dur

                itinerary.append({
                    "action": "meet",
                    "location": fr["location"],
                    "person": fr["name"],
                    "start_time": time_to_str(meet_start),
                    "end_time": time_to_str(meet_end),
                })

                backtrack(fr["location"], meet_end, met_mask | (1 << i), itinerary)

                itinerary.pop()

    backtrack(start_location, start_time, 0, [])
    return best_itinerary

def main():
    # Input parameters (can be modified as needed)
    arrival_location = "Fisherman's Wharf"
    arrival_time = "9:00"

    travel_times = {
        ("Fisherman's Wharf", "Nob Hill"): 11,
        ("Nob Hill", "Fisherman's Wharf"): 11,
    }

    friends = [
        {
            "name": "Kenneth",
            "location": "Nob Hill",
            "start": "14:15",
            "end": "19:45",
            "min_meet": 90
        }
    ]

    itinerary = plan_schedule(arrival_location, arrival_time, travel_times, friends)

    output = {
        "itinerary": itinerary
    }
    print(json.dumps(output, ensure_ascii=False, indent=2))

if __name__ == "__main__":
    main()