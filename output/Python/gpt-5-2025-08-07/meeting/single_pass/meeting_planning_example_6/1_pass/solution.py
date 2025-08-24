import json
from typing import Dict, Tuple, List, Optional

# Helper functions for time handling
def parse_time(t: str) -> int:
    # t format: 'H:MM' or 'HH:MM' 24-hour
    h, m = t.split(":")
    return int(h) * 60 + int(m)

def fmt_time(minutes: int) -> str:
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

# Input parameters (as variables)
origin_location = "Fisherman's Wharf"
arrival_time_at_origin_str = "9:00"  # arriving at Fisherman's Wharf at 9:00AM
arrival_time_at_origin = parse_time(arrival_time_at_origin_str)

# Friend availability and constraints
friends = [
    {
        "name": "Kenneth",
        "location": "Nob Hill",
        "available_start": "14:15",
        "available_end": "19:45",
        "min_meet_minutes": 90
    }
]

# Travel times (in minutes)
travel_times: Dict[Tuple[str, str], int] = {
    ("Fisherman's Wharf", "Nob Hill"): 11,
    ("Nob Hill", "Fisherman's Wharf"): 11
}

def get_travel_time(a: str, b: str) -> Optional[int]:
    return travel_times.get((a, b), None)

# Objective: meet as many friends as possible.
# Since only one friend is given, we maximize the meeting duration with them
# and ensure minimum duration is satisfied. We also consider various departure
# schedules and pick the best (max duration, then minimal waiting).

def plan_meeting_with_friend(origin_loc: str, origin_arrival: int, friend: dict):
    friend_loc = friend["location"]
    start = parse_time(friend["available_start"])
    end = parse_time(friend["available_end"])
    min_meet = friend["min_meet_minutes"]
    tt = get_travel_time(origin_loc, friend_loc)
    if tt is None:
        return None

    # Enumerate possible departure times by the minute from arrival to latest feasible departure
    latest_departure = end - tt  # depart so that arrival <= end
    if latest_departure < origin_arrival:
        return None

    best = None
    for depart in range(origin_arrival, latest_departure + 1):
        arrive = depart + tt
        # Meeting can only happen within friend's availability and after arrival
        meet_start = max(arrive, start)
        meet_end = end
        if meet_end <= meet_start:
            duration = 0
        else:
            duration = meet_end - meet_start

        if duration >= min_meet:
            waiting = max(0, start - arrive)  # if we arrive before start, we wait
            candidate = {
                "depart": depart,
                "arrive": arrive,
                "meet_start": meet_start,
                "meet_end": meet_end,
                "duration": duration,
                "waiting": waiting
            }
            if best is None:
                best = candidate
            else:
                # Primary: maximize duration
                if candidate["duration"] > best["duration"]:
                    best = candidate
                elif candidate["duration"] == best["duration"]:
                    # Secondary: minimize waiting
                    if candidate["waiting"] < best["waiting"]:
                        best = candidate
                    elif candidate["waiting"] == best["waiting"]:
                        # Tertiary: earliest meeting start
                        if candidate["meet_start"] < best["meet_start"]:
                            best = candidate
                        elif candidate["meet_start"] == best["meet_start"]:
                            # Quaternary: latest departure (to avoid waiting later in the day)
                            if candidate["depart"] > best["depart"]:
                                best = candidate

    if best is None:
        return None

    return {
        "action": "meet",
        "location": friend_loc,
        "person": friend["name"],
        "start_time": fmt_time(best["meet_start"]),
        "end_time": fmt_time(best["meet_end"])
    }

def compute_itinerary():
    itinerary: List[dict] = []

    # Evaluate each friend independently (only Kenneth provided).
    # Select all feasible meetings maximizing count; given only one friend, include if feasible.
    feasible_meetings = []
    for f in friends:
        meeting = plan_meeting_with_friend(origin_location, arrival_time_at_origin, f)
        if meeting:
            feasible_meetings.append((f["name"], meeting))

    # With only one friend, optimal is to include that meeting if feasible
    if feasible_meetings:
        itinerary.append(feasible_meetings[0][1])

    return {"itinerary": itinerary}

if __name__ == "__main__":
    result = compute_itinerary()
    print(json.dumps(result, ensure_ascii=False))