import json
from functools import lru_cache
from dataclasses import dataclass

# Utility functions for time handling
def hm_to_min(h, m):
    return h * 60 + m

def min_to_hm_str(t):
    h = t // 60
    m = t % 60
    return f"{h}:{m:02d}"

@dataclass(frozen=True)
class Person:
    name: str
    location: str
    start: int
    end: int
    min_duration: int

def build_travel_times():
    T = {
        "Russian Hill": {
            "Pacific Heights": 7,
            "North Beach": 5,
            "Golden Gate Park": 21,
            "Embarcadero": 8,
            "Haight-Ashbury": 17,
            "Fisherman's Wharf": 7,
            "Mission District": 16,
            "Alamo Square": 15,
            "Bayview": 23,
            "Richmond District": 14,
        },
        "Pacific Heights": {
            "Russian Hill": 7,
            "North Beach": 9,
            "Golden Gate Park": 15,
            "Embarcadero": 10,
            "Haight-Ashbury": 11,
            "Fisherman's Wharf": 13,
            "Mission District": 15,
            "Alamo Square": 10,
            "Bayview": 22,
            "Richmond District": 12,
        },
        "North Beach": {
            "Russian Hill": 4,
            "Pacific Heights": 8,
            "Golden Gate Park": 22,
            "Embarcadero": 6,
            "Haight-Ashbury": 18,
            "Fisherman's Wharf": 5,
            "Mission District": 18,
            "Alamo Square": 16,
            "Bayview": 25,
            "Richmond District": 18,
        },
        "Golden Gate Park": {
            "Russian Hill": 19,
            "Pacific Heights": 16,
            "North Beach": 23,
            "Embarcadero": 25,
            "Haight-Ashbury": 7,
            "Fisherman's Wharf": 24,
            "Mission District": 17,
            "Alamo Square": 9,
            "Bayview": 23,
            "Richmond District": 7,
        },
        "Embarcadero": {
            "Russian Hill": 8,
            "Pacific Heights": 11,
            "North Beach": 5,
            "Golden Gate Park": 25,
            "Haight-Ashbury": 21,
            "Fisherman's Wharf": 6,
            "Mission District": 20,
            "Alamo Square": 19,
            "Bayview": 21,
            "Richmond District": 21,
        },
        "Haight-Ashbury": {
            "Russian Hill": 17,
            "Pacific Heights": 12,
            "North Beach": 19,
            "Golden Gate Park": 7,
            "Embarcadero": 20,
            "Fisherman's Wharf": 23,
            "Mission District": 11,
            "Alamo Square": 5,
            "Bayview": 18,
            "Richmond District": 10,
        },
        "Fisherman's Wharf": {
            "Russian Hill": 7,
            "Pacific Heights": 12,
            "North Beach": 6,
            "Golden Gate Park": 25,
            "Embarcadero": 8,
            "Haight-Ashbury": 22,
            "Mission District": 22,
            "Alamo Square": 21,
            "Bayview": 26,
            "Richmond District": 18,
        },
        "Mission District": {
            "Russian Hill": 15,
            "Pacific Heights": 16,
            "North Beach": 17,
            "Golden Gate Park": 17,
            "Embarcadero": 19,
            "Haight-Ashbury": 12,
            "Fisherman's Wharf": 22,
            "Alamo Square": 11,
            "Bayview": 14,
            "Richmond District": 20,
        },
        "Alamo Square": {
            "Russian Hill": 13,
            "Pacific Heights": 10,
            "North Beach": 15,
            "Golden Gate Park": 9,
            "Embarcadero": 16,
            "Haight-Ashbury": 5,
            "Fisherman's Wharf": 19,
            "Mission District": 10,
            "Bayview": 16,
            "Richmond District": 11,
        },
        "Bayview": {
            "Russian Hill": 23,
            "Pacific Heights": 23,
            "North Beach": 22,
            "Golden Gate Park": 22,
            "Embarcadero": 19,
            "Haight-Ashbury": 19,
            "Fisherman's Wharf": 25,
            "Mission District": 13,
            "Alamo Square": 16,
            "Richmond District": 25,
        },
        "Richmond District": {
            "Russian Hill": 13,
            "Pacific Heights": 10,
            "North Beach": 17,
            "Golden Gate Park": 9,
            "Embarcadero": 19,
            "Haight-Ashbury": 10,
            "Fisherman's Wharf": 18,
            "Mission District": 20,
            "Alamo Square": 13,
            "Bayview": 27,
        },
    }
    # Ensure self travel is zero for completeness
    for a in T:
        T[a][a] = 0
    return T

def build_people():
    return [
        Person("Emily", "Pacific Heights", hm_to_min(9,15), hm_to_min(13,45), 120),
        Person("Helen", "North Beach", hm_to_min(13,45), hm_to_min(18,45), 30),
        Person("Kimberly", "Golden Gate Park", hm_to_min(18,45), hm_to_min(21,15), 75),
        Person("James", "Embarcadero", hm_to_min(10,30), hm_to_min(11,30), 30),
        Person("Linda", "Haight-Ashbury", hm_to_min(7,30), hm_to_min(19,15), 15),
        Person("Paul", "Fisherman's Wharf", hm_to_min(14,45), hm_to_min(18,45), 90),
        Person("Anthony", "Mission District", hm_to_min(8,0), hm_to_min(14,45), 105),
        Person("Nancy", "Alamo Square", hm_to_min(8,30), hm_to_min(13,45), 120),
        Person("William", "Bayview", hm_to_min(17,30), hm_to_min(20,30), 120),
        Person("Margaret", "Richmond District", hm_to_min(15,15), hm_to_min(18,15), 45),
    ]

def main():
    # Inputs
    start_location = "Russian Hill"
    start_time = hm_to_min(9, 0)  # 9:00
    travel = build_travel_times()
    people = build_people()
    idx_map = {i: p for i, p in enumerate(people)}
    n = len(people)

    # For caching, we need a stable ordering of persons
    # We'll iterate in order of earliest window end to help pruning but still explore all
    order = sorted(range(n), key=lambda i: (people[i].end, people[i].start))

    @lru_cache(maxsize=None)
    def dfs(current_loc, current_time, visited_mask):
        best_score = (0, 0, 0, 0)  # (count, total_meet, -total_travel, -total_wait)
        best_plan = tuple()

        for i in order:
            if visited_mask & (1 << i):
                continue
            p = people[i]
            # Travel time
            t_travel = travel[current_loc][p.location]
            arrival = current_time + t_travel
            start = max(arrival, p.start)
            end = start + p.min_duration
            if end > p.end:
                continue  # infeasible
            wait = max(0, start - arrival)

            child_score, child_plan = dfs(p.location, end, visited_mask | (1 << i))

            cand_score = (
                child_score[0] + 1,
                child_score[1] + p.min_duration,
                child_score[2] - t_travel,
                child_score[3] - wait,
            )

            if cand_score > best_score:
                best_score = cand_score
                meeting_tuple = (p.location, p.name, start, end)
                best_plan = (meeting_tuple,) + child_plan

        return best_score, best_plan

    best_score, best_plan = dfs(start_location, start_time, 0)

    # Build JSON itinerary
    itinerary = []
    for loc, person_name, st, et in best_plan:
        itinerary.append({
            "action": "meet",
            "location": loc,
            "person": person_name,
            "start_time": min_to_hm_str(st),
            "end_time": min_to_hm_str(et),
        })

    output = {"itinerary": itinerary}
    print(json.dumps(output, ensure_ascii=False, indent=2))

if __name__ == "__main__":
    main()