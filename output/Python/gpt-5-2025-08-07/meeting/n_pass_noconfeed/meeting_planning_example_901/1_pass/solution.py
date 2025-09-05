import json
from dataclasses import dataclass
from typing import Dict, List, Tuple

# Helper to convert H:MM string to minutes from midnight
def t2m(s: str) -> int:
    h, m = s.split(":")
    return int(h) * 60 + int(m)

# Helper to convert minutes to H:MM string without leading zero for hour
def m2t(m: int) -> str:
    h = m // 60
    mm = m % 60
    return f"{h}:{mm:02d}"

@dataclass(frozen=True)
class Person:
    name: str
    location: str
    start: int
    end: int
    min_minutes: int

def build_travel_times() -> Dict[str, Dict[str, int]]:
    locs = [
        "Russian Hill",
        "Pacific Heights",
        "North Beach",
        "Golden Gate Park",
        "Embarcadero",
        "Haight-Ashbury",
        "Fisherman's Wharf",
        "Mission District",
        "Alamo Square",
        "Bayview",
        "Richmond District",
    ]
    # Initialize with 0 for same-location travel
    travel = {a: {b: (0 if a == b else None) for b in locs} for a in locs}

    def set_time(a, b, t):
        travel[a][b] = t

    # Given directed travel times (in minutes)
    set_time("Russian Hill", "Pacific Heights", 7)
    set_time("Russian Hill", "North Beach", 5)
    set_time("Russian Hill", "Golden Gate Park", 21)
    set_time("Russian Hill", "Embarcadero", 8)
    set_time("Russian Hill", "Haight-Ashbury", 17)
    set_time("Russian Hill", "Fisherman's Wharf", 7)
    set_time("Russian Hill", "Mission District", 16)
    set_time("Russian Hill", "Alamo Square", 15)
    set_time("Russian Hill", "Bayview", 23)
    set_time("Russian Hill", "Richmond District", 14)

    set_time("Pacific Heights", "Russian Hill", 7)
    set_time("Pacific Heights", "North Beach", 9)
    set_time("Pacific Heights", "Golden Gate Park", 15)
    set_time("Pacific Heights", "Embarcadero", 10)
    set_time("Pacific Heights", "Haight-Ashbury", 11)
    set_time("Pacific Heights", "Fisherman's Wharf", 13)
    set_time("Pacific Heights", "Mission District", 15)
    set_time("Pacific Heights", "Alamo Square", 10)
    set_time("Pacific Heights", "Bayview", 22)
    set_time("Pacific Heights", "Richmond District", 12)

    set_time("North Beach", "Russian Hill", 4)
    set_time("North Beach", "Pacific Heights", 8)
    set_time("North Beach", "Golden Gate Park", 22)
    set_time("North Beach", "Embarcadero", 6)
    set_time("North Beach", "Haight-Ashbury", 18)
    set_time("North Beach", "Fisherman's Wharf", 5)
    set_time("North Beach", "Mission District", 18)
    set_time("North Beach", "Alamo Square", 16)
    set_time("North Beach", "Bayview", 25)
    set_time("North Beach", "Richmond District", 18)

    set_time("Golden Gate Park", "Russian Hill", 19)
    set_time("Golden Gate Park", "Pacific Heights", 16)
    set_time("Golden Gate Park", "North Beach", 23)
    set_time("Golden Gate Park", "Embarcadero", 25)
    set_time("Golden Gate Park", "Haight-Ashbury", 7)
    set_time("Golden Gate Park", "Fisherman's Wharf", 24)
    set_time("Golden Gate Park", "Mission District", 17)
    set_time("Golden Gate Park", "Alamo Square", 9)
    set_time("Golden Gate Park", "Bayview", 23)
    set_time("Golden Gate Park", "Richmond District", 7)

    set_time("Embarcadero", "Russian Hill", 8)
    set_time("Embarcadero", "Pacific Heights", 11)
    set_time("Embarcadero", "North Beach", 5)
    set_time("Embarcadero", "Golden Gate Park", 25)
    set_time("Embarcadero", "Haight-Ashbury", 21)
    set_time("Embarcadero", "Fisherman's Wharf", 6)
    set_time("Embarcadero", "Mission District", 20)
    set_time("Embarcadero", "Alamo Square", 19)
    set_time("Embarcadero", "Bayview", 21)
    set_time("Embarcadero", "Richmond District", 21)

    set_time("Haight-Ashbury", "Russian Hill", 17)
    set_time("Haight-Ashbury", "Pacific Heights", 12)
    set_time("Haight-Ashbury", "North Beach", 19)
    set_time("Haight-Ashbury", "Golden Gate Park", 7)
    set_time("Haight-Ashbury", "Embarcadero", 20)
    set_time("Haight-Ashbury", "Fisherman's Wharf", 23)
    set_time("Haight-Ashbury", "Mission District", 11)
    set_time("Haight-Ashbury", "Alamo Square", 5)
    set_time("Haight-Ashbury", "Bayview", 18)
    set_time("Haight-Ashbury", "Richmond District", 10)

    set_time("Fisherman's Wharf", "Russian Hill", 7)
    set_time("Fisherman's Wharf", "Pacific Heights", 12)
    set_time("Fisherman's Wharf", "North Beach", 6)
    set_time("Fisherman's Wharf", "Golden Gate Park", 25)
    set_time("Fisherman's Wharf", "Embarcadero", 8)
    set_time("Fisherman's Wharf", "Haight-Ashbury", 22)
    set_time("Fisherman's Wharf", "Mission District", 22)
    set_time("Fisherman's Wharf", "Alamo Square", 21)
    set_time("Fisherman's Wharf", "Bayview", 26)
    set_time("Fisherman's Wharf", "Richmond District", 18)

    set_time("Mission District", "Russian Hill", 15)
    set_time("Mission District", "Pacific Heights", 16)
    set_time("Mission District", "North Beach", 17)
    set_time("Mission District", "Golden Gate Park", 17)
    set_time("Mission District", "Embarcadero", 19)
    set_time("Mission District", "Haight-Ashbury", 12)
    set_time("Mission District", "Fisherman's Wharf", 22)
    set_time("Mission District", "Alamo Square", 11)
    set_time("Mission District", "Bayview", 14)
    set_time("Mission District", "Richmond District", 20)

    set_time("Alamo Square", "Russian Hill", 13)
    set_time("Alamo Square", "Pacific Heights", 10)
    set_time("Alamo Square", "North Beach", 15)
    set_time("Alamo Square", "Golden Gate Park", 9)
    set_time("Alamo Square", "Embarcadero", 16)
    set_time("Alamo Square", "Haight-Ashbury", 5)
    set_time("Alamo Square", "Fisherman's Wharf", 19)
    set_time("Alamo Square", "Mission District", 10)
    set_time("Alamo Square", "Bayview", 16)
    set_time("Alamo Square", "Richmond District", 11)

    set_time("Bayview", "Russian Hill", 23)
    set_time("Bayview", "Pacific Heights", 23)
    set_time("Bayview", "North Beach", 22)
    set_time("Bayview", "Golden Gate Park", 22)
    set_time("Bayview", "Embarcadero", 19)
    set_time("Bayview", "Haight-Ashbury", 19)
    set_time("Bayview", "Fisherman's Wharf", 25)
    set_time("Bayview", "Mission District", 13)
    set_time("Bayview", "Alamo Square", 16)
    set_time("Bayview", "Richmond District", 25)

    set_time("Richmond District", "Russian Hill", 13)
    set_time("Richmond District", "Pacific Heights", 10)
    set_time("Richmond District", "North Beach", 17)
    set_time("Richmond District", "Golden Gate Park", 9)
    set_time("Richmond District", "Embarcadero", 19)
    set_time("Richmond District", "Haight-Ashbury", 10)
    set_time("Richmond District", "Fisherman's Wharf", 18)
    set_time("Richmond District", "Mission District", 20)
    set_time("Richmond District", "Alamo Square", 13)
    set_time("Richmond District", "Bayview", 27)

    # Validate none are None
    for a in travel:
        for b in travel[a]:
            if travel[a][b] is None:
                raise ValueError(f"Missing travel time from {a} to {b}")
    return travel

def build_people() -> List[Person]:
    friends = [
        Person("Emily", "Pacific Heights", t2m("9:15"), t2m("13:45"), 120),
        Person("Helen", "North Beach", t2m("13:45"), t2m("18:45"), 30),
        Person("Kimberly", "Golden Gate Park", t2m("18:45"), t2m("21:15"), 75),
        Person("James", "Embarcadero", t2m("10:30"), t2m("11:30"), 30),
        Person("Linda", "Haight-Ashbury", t2m("7:30"), t2m("19:15"), 15),
        Person("Paul", "Fisherman's Wharf", t2m("14:45"), t2m("18:45"), 90),
        Person("Anthony", "Mission District", t2m("8:00"), t2m("14:45"), 105),
        Person("Nancy", "Alamo Square", t2m("8:30"), t2m("13:45"), 120),
        Person("William", "Bayview", t2m("17:30"), t2m("20:30"), 120),
        Person("Margaret", "Richmond District", t2m("15:15"), t2m("18:15"), 45),
    ]
    return friends

def compute_optimal_itinerary():
    # Inputs
    start_location = "Russian Hill"
    arrival_time = t2m("9:00")

    travel = build_travel_times()
    people = build_people()
    idx = {p.name: i for i, p in enumerate(people)}

    n = len(people)

    # Pre-calc for faster lookups
    def possible_from(loc: str, time: int, p: Person) -> Tuple[bool, int, int]:
        arr = time + travel[loc][p.location]
        start = max(arr, p.start)
        end = start + p.min_minutes
        feasible = end <= p.end
        return feasible, start, end

    best_itin: List[Dict] = []
    best_count = -1
    best_end_time = float('inf')
    best_travel_sum = float('inf')

    # Memo: earliest time seen for (loc, met_mask) to prune dominated states
    seen_earliest: Dict[Tuple[str, int], int] = {}

    def dfs(loc: str, time: int, met_mask: int, itin: List[Dict], travel_sum: int):
        nonlocal best_itin, best_count, best_end_time, best_travel_sum

        current_count = bin(met_mask).count("1")

        # Prune dominated states
        key = (loc, met_mask)
        prev = seen_earliest.get(key)
        if prev is not None and time >= prev:
            return
        seen_earliest[key] = time

        # Upper bound on achievable count: optimistic feasibility check from current state
        bound = current_count
        for i, p in enumerate(people):
            if not (met_mask & (1 << i)):
                arr = time + travel[loc][p.location]
                latest_start = p.end - p.min_minutes
                if arr <= latest_start:
                    bound += 1
        if bound < best_count:
            return

        # Update best solution at leaf or intermediate
        improved = False
        if current_count > best_count:
            improved = True
        elif current_count == best_count:
            # Tie-breaker: earlier finish time, then lower travel sum, then lexicographic by itinerary
            if time < best_end_time:
                improved = True
            elif time == best_end_time and travel_sum < best_travel_sum:
                improved = True

        if improved:
            best_count = current_count
            best_end_time = time
            best_travel_sum = travel_sum
            best_itin = [dict(x) for x in itin]

        # Generate feasible next meetings
        candidates = []
        for i, p in enumerate(people):
            if met_mask & (1 << i):
                continue
            feasible, start_t, end_t = possible_from(loc, time, p)
            if feasible:
                cand_travel = travel[loc][p.location]
                candidates.append((i, p, start_t, end_t, cand_travel))

        # Heuristic ordering: earliest finishing first, then earliest start, then shorter travel
        candidates.sort(key=lambda x: (x[3], x[2], x[4]))

        for i, p, start_t, end_t, cand_travel in candidates:
            # Build next itinerary entry
            entry = {
                "action": "meet",
                "location": p.location,
                "person": p.name,
                "start_time": m2t(start_t),
                "end_time": m2t(end_t),
            }
            itin.append(entry)
            dfs(p.location, end_t, met_mask | (1 << i), itin, travel_sum + cand_travel)
            itin.pop()

    dfs(start_location, arrival_time, 0, [], 0)

    # Build final JSON
    result = {"itinerary": best_itin}
    print(json.dumps(result, ensure_ascii=False, indent=2))

if __name__ == "__main__":
    compute_optimal_itinerary()