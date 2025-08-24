import itertools
import json
from typing import Dict, List, Tuple, Optional

# Utility functions for time handling
def parse_time_str(s: str) -> int:
    s = s.strip().upper()
    # Expected formats like '9:00AM', '4:30PM'
    if s.endswith("AM"):
        ampm = "AM"
        s = s[:-2]
    elif s.endswith("PM"):
        ampm = "PM"
        s = s[:-2]
    else:
        raise ValueError(f"Time must end with AM/PM: {s}")
    hour_str, minute_str = s.split(":")
    hour = int(hour_str)
    minute = int(minute_str)
    if ampm == "AM":
        if hour == 12:
            hour = 0
    else:  # PM
        if hour != 12:
            hour += 12
    return hour * 60 + minute

def fmt_time(m: int) -> str:
    hour = m // 60
    minute = m % 60
    return f"{hour}:{minute:02d}"

# Input variables (meeting constraints)
arrival_location = "Nob Hill"
arrival_time_str = "9:00AM"
arrival_time = parse_time_str(arrival_time_str)

people = {
    "Emily": {
        "location": "Richmond District",
        "window_start": parse_time_str("7:00PM"),
        "window_end": parse_time_str("9:00PM"),
        "min_duration": 15,
    },
    "Margaret": {
        "location": "Financial District",
        "window_start": parse_time_str("4:30PM"),
        "window_end": parse_time_str("8:15PM"),
        "min_duration": 75,
    },
    "Ronald": {
        "location": "North Beach",
        "window_start": parse_time_str("6:30PM"),
        "window_end": parse_time_str("7:30PM"),
        "min_duration": 45,
    },
    "Deborah": {
        "location": "The Castro",
        "window_start": parse_time_str("1:45PM"),
        "window_end": parse_time_str("9:15PM"),
        "min_duration": 90,
    },
    "Jeffrey": {
        "location": "Golden Gate Park",
        "window_start": parse_time_str("11:15AM"),
        "window_end": parse_time_str("2:30PM"),
        "min_duration": 120,
    },
}

# Directed travel times (in minutes)
travel_times: Dict[str, Dict[str, int]] = {
    "Nob Hill": {
        "Richmond District": 14,
        "Financial District": 9,
        "North Beach": 8,
        "The Castro": 17,
        "Golden Gate Park": 17,
    },
    "Richmond District": {
        "Nob Hill": 17,
        "Financial District": 22,
        "North Beach": 17,
        "The Castro": 16,
        "Golden Gate Park": 9,
    },
    "Financial District": {
        "Nob Hill": 8,
        "Richmond District": 21,
        "North Beach": 7,
        "The Castro": 23,
        "Golden Gate Park": 23,
    },
    "North Beach": {
        "Nob Hill": 7,
        "Richmond District": 18,
        "Financial District": 8,
        "The Castro": 22,
        "Golden Gate Park": 22,
    },
    "The Castro": {
        "Nob Hill": 16,
        "Richmond District": 16,
        "Financial District": 20,
        "North Beach": 20,
        "Golden Gate Park": 11,
    },
    "Golden Gate Park": {
        "Nob Hill": 20,
        "Richmond District": 7,
        "Financial District": 26,
        "North Beach": 24,
        "The Castro": 13,
    },
}

def travel_time(src: str, dst: str) -> Optional[int]:
    if src == dst:
        return 0
    return travel_times.get(src, {}).get(dst, None)

# Scheduling logic
def schedule_order(order: Tuple[str, ...]) -> Optional[Tuple[List[dict], int, int, int, int]]:
    """
    Attempt to schedule the given order of people.
    Returns (itinerary, total_meeting_time, total_travel_time, total_idle_time, finish_time)
    or None if infeasible.
    """
    current_loc = arrival_location
    current_time = arrival_time
    itinerary = []
    total_meeting_time = 0
    total_travel_time = 0
    total_idle_time = 0

    for person in order:
        info = people[person]
        loc = info["location"]
        t_travel = travel_time(current_loc, loc)
        if t_travel is None:
            return None  # missing travel time; treat as infeasible

        arrival = current_time + t_travel
        ws = info["window_start"]
        we = info["window_end"]
        dur = info["min_duration"]

        # If even starting at arrival can't fit, try to start at window start if later
        # Compute feasible start
        start = max(arrival, ws)
        if start + dur > we:
            return None

        idle = max(0, start - arrival)
        end = start + dur

        itinerary.append({
            "action": "meet",
            "location": loc,
            "person": person,
            "start_time": fmt_time(start),
            "end_time": fmt_time(end),
        })

        total_meeting_time += dur
        total_travel_time += t_travel
        total_idle_time += idle

        current_loc = loc
        current_time = end

    finish_time = current_time
    return itinerary, total_meeting_time, total_travel_time, total_idle_time, finish_time

def choose_best_schedule() -> List[dict]:
    names = list(people.keys())
    best = None  # tuple: (num_meetings, -total_meeting_time, total_idle_time, finish_time, total_travel_time, itinerary, order_signature)
    # Since total_meeting_time is fixed given subset (sum of mins), we can keep as secondary sanity metric
    for r in range(len(names), 0, -1):  # try larger subsets first
        found_for_size = False
        for subset in itertools.combinations(names, r):
            # Sort to create a stable tie-breaker later
            for perm in itertools.permutations(subset):
                res = schedule_order(perm)
                if res is None:
                    continue
                itinerary, total_meet, total_travel, total_idle, finish = res
                # Objective: maximize number of meetings, then minimize idle, then earliest finish, then minimize travel, then lexicographic order
                score = (
                    len(perm),
                    -total_idle,          # higher is better (less idle)
                    -finish,              # earlier finish preferred
                    -total_meet,          # larger meeting time preferred (though fixed)
                    -sum(ord(c) for c in "".join(perm)),  # stable but arbitrary
                    - (1 if perm < tuple(sorted(perm)) else 0), # slight bias to earlier lexicographic order
                )
                candidate = (score, itinerary)
                if best is None or candidate[0] > best[0]:
                    best = candidate
                    found_for_size = True
        if found_for_size and best:
            # Since we iterate r from large to small, once we found at least one feasible for this size,
            # we can still check other subsets of same size (already done),
            # but after finishing this size, we can break to return the best of this maximal size.
            # However, because we already iterated all subsets/perms for this r, we can return now.
            pass
        if best is not None and best[0][0] == r:
            # best found for current maximal r
            # continue loop to ensure no other r (smaller) will surpass, but they can't due to primary objective
            break

    return best[1] if best else []

def main():
    itinerary = choose_best_schedule()
    output = {"itinerary": itinerary}
    print(json.dumps(output, ensure_ascii=False))

if __name__ == "__main__":
    main()