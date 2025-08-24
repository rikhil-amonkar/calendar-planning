import json
from functools import lru_cache
from dataclasses import dataclass

# Helper to format minutes since midnight into 'H:MM' 24-hour format without leading zero
def fmt_time(m):
    h = m // 60
    mn = m % 60
    return f"{h}:{mn:02d}"

@dataclass(frozen=True)
class Person:
    name: str
    location: str
    start: int   # minutes from midnight
    end: int     # minutes from midnight
    min_dur: int # minutes

def build_data():
    # Travel times in minutes between locations
    travel = {
        "Mission District": {
            "Alamo Square": 11, "Presidio": 25, "Russian Hill": 15, "North Beach": 17,
            "Golden Gate Park": 17, "Richmond District": 20, "Embarcadero": 19,
            "Financial District": 15, "Marina District": 19
        },
        "Alamo Square": {
            "Mission District": 10, "Presidio": 17, "Russian Hill": 13, "North Beach": 15,
            "Golden Gate Park": 9, "Richmond District": 11, "Embarcadero": 16,
            "Financial District": 17, "Marina District": 15
        },
        "Presidio": {
            "Mission District": 26, "Alamo Square": 19, "Russian Hill": 14, "North Beach": 18,
            "Golden Gate Park": 12, "Richmond District": 7, "Embarcadero": 20,
            "Financial District": 23, "Marina District": 11
        },
        "Russian Hill": {
            "Mission District": 16, "Alamo Square": 15, "Presidio": 14, "North Beach": 5,
            "Golden Gate Park": 21, "Richmond District": 14, "Embarcadero": 8,
            "Financial District": 11, "Marina District": 7
        },
        "North Beach": {
            "Mission District": 18, "Alamo Square": 16, "Presidio": 17, "Russian Hill": 4,
            "Golden Gate Park": 22, "Richmond District": 18, "Embarcadero": 6,
            "Financial District": 8, "Marina District": 9
        },
        "Golden Gate Park": {
            "Mission District": 17, "Alamo Square": 9, "Presidio": 11, "Russian Hill": 19,
            "North Beach": 23, "Richmond District": 7, "Embarcadero": 25,
            "Financial District": 26, "Marina District": 16
        },
        "Richmond District": {
            "Mission District": 20, "Alamo Square": 13, "Presidio": 7, "Russian Hill": 13,
            "North Beach": 17, "Golden Gate Park": 9, "Embarcadero": 19,
            "Financial District": 22, "Marina District": 9
        },
        "Embarcadero": {
            "Mission District": 20, "Alamo Square": 19, "Presidio": 20, "Russian Hill": 8,
            "North Beach": 5, "Golden Gate Park": 25, "Richmond District": 21,
            "Financial District": 5, "Marina District": 12
        },
        "Financial District": {
            "Mission District": 17, "Alamo Square": 17, "Presidio": 22, "Russian Hill": 11,
            "North Beach": 7, "Golden Gate Park": 23, "Richmond District": 21,
            "Embarcadero": 4, "Marina District": 15
        },
        "Marina District": {
            "Mission District": 20, "Alamo Square": 15, "Presidio": 10, "Russian Hill": 8,
            "North Beach": 11, "Golden Gate Park": 18, "Richmond District": 11,
            "Embarcadero": 14, "Financial District": 17
        },
    }

    # People constraints (minutes since midnight)
    def t(h, m): return h * 60 + m

    people = [
        Person("Laura", "Alamo Square", t(14, 30), t(16, 15), 75),
        Person("Brian", "Presidio", t(10, 15), t(17, 0), 30),
        Person("Karen", "Russian Hill", t(18, 0), t(20, 15), 90),
        Person("Stephanie", "North Beach", t(10, 15), t(16, 0), 75),
        Person("Helen", "Golden Gate Park", t(11, 30), t(21, 45), 120),
        Person("Sandra", "Richmond District", t(8, 0), t(15, 15), 30),
        Person("Mary", "Embarcadero", t(16, 45), t(18, 45), 120),
        Person("Deborah", "Financial District", t(19, 0), t(20, 45), 105),
        Person("Elizabeth", "Marina District", t(8, 30), t(13, 15), 105),
    ]

    return travel, people

def main():
    travel, people = build_data()

    # Initial state
    start_location = "Mission District"
    start_time = 9 * 60  # 9:00

    N = len(people)

    # map index to person for bitmasking
    idx_to_person = {i: p for i, p in enumerate(people)}

    # Cache: key -> (loc, time, remaining_mask) -> (count, meet_minutes, travel_minutes, finish_time, itinerary_list)
    @lru_cache(maxsize=None)
    def dfs(current_loc: str, current_time: int, remaining_mask: int):
        best = (0, 0, 0, current_time, [])  # count, meet_minutes, travel_minutes, finish_time, itinerary
        # Try scheduling each remaining person next
        for i in range(N):
            if not (remaining_mask & (1 << i)):
                continue
            p = idx_to_person[i]

            # Travel time from current_loc to p.location
            if current_loc == p.location:
                dtravel = 0
            else:
                # Some pairs may not be present due to data entry, guard
                if current_loc not in travel or p.location not in travel[current_loc]:
                    continue
                dtravel = travel[current_loc][p.location]

            arrival = current_time + dtravel
            start_meet = max(arrival, p.start)
            end_meet = start_meet + p.min_dur
            if end_meet > p.end:
                continue  # infeasible

            # Recurse after this meeting
            rem_mask2 = remaining_mask & ~(1 << i)
            cnt2, meet2, trav2, fin2, itin2 = dfs(p.location, end_meet, rem_mask2)

            cnt = 1 + cnt2
            meet = p.min_dur + meet2
            trav = dtravel + trav2
            finish_time = fin2 if cnt2 > 0 else end_meet

            # Tie-breakers: maximize (cnt, meet, -trav, -finish_time)
            cand_key = (cnt, meet, -trav, -finish_time)
            best_key = (best[0], best[1], -best[2], -best[3])
            if cand_key > best_key:
                # Build itinerary entry
                entry = {
                    "action": "meet",
                    "location": p.location,
                    "person": p.name,
                    "start_time": fmt_time(start_meet),
                    "end_time": fmt_time(end_meet),
                }
                best = (cnt, meet, trav, finish_time, [entry] + itin2)

        return best

    remaining_all = (1 << N) - 1
    cnt, meet_min, trav_min, finish, itin = dfs(start_location, start_time, remaining_all)

    # The itinerary produced is already chronological because we always move forward in time.
    result = {"itinerary": itin}
    print(json.dumps(result, ensure_ascii=False))

if __name__ == "__main__":
    main()