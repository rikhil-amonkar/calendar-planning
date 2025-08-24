import json
from functools import lru_cache

def fmt_time(m):
    h = m // 60
    mm = m % 60
    return f"{h}:{mm:02d}"

def main():
    # Locations
    locations = [
        "Fisherman's Wharf", "The Castro", "Golden Gate Park", "Embarcadero",
        "Russian Hill", "Nob Hill", "Alamo Square", "North Beach"
    ]

    # Directed travel times in minutes
    T = {
        "Fisherman's Wharf": {
            "The Castro": 26, "Golden Gate Park": 25, "Embarcadero": 8,
            "Russian Hill": 7, "Nob Hill": 11, "Alamo Square": 20, "North Beach": 6
        },
        "The Castro": {
            "Fisherman's Wharf": 24, "Golden Gate Park": 11, "Embarcadero": 22,
            "Russian Hill": 18, "Nob Hill": 16, "Alamo Square": 8, "North Beach": 20
        },
        "Golden Gate Park": {
            "Fisherman's Wharf": 24, "The Castro": 13, "Embarcadero": 25,
            "Russian Hill": 19, "Nob Hill": 20, "Alamo Square": 10, "North Beach": 24
        },
        "Embarcadero": {
            "Fisherman's Wharf": 6, "The Castro": 25, "Golden Gate Park": 25,
            "Russian Hill": 8, "Nob Hill": 10, "Alamo Square": 19, "North Beach": 5
        },
        "Russian Hill": {
            "Fisherman's Wharf": 7, "The Castro": 21, "Golden Gate Park": 21,
            "Embarcadero": 8, "Nob Hill": 5, "Alamo Square": 15, "North Beach": 5
        },
        "Nob Hill": {
            "Fisherman's Wharf": 11, "The Castro": 17, "Golden Gate Park": 17,
            "Embarcadero": 9, "Russian Hill": 5, "Alamo Square": 11, "North Beach": 8
        },
        "Alamo Square": {
            "Fisherman's Wharf": 19, "The Castro": 8, "Golden Gate Park": 9,
            "Embarcadero": 17, "Russian Hill": 13, "Nob Hill": 11, "North Beach": 15
        },
        "North Beach": {
            "Fisherman's Wharf": 5, "The Castro": 22, "Golden Gate Park": 22,
            "Embarcadero": 6, "Russian Hill": 4, "Nob Hill": 7, "Alamo Square": 16
        }
    }

    # Friends and constraints
    # Times in minutes from midnight
    def m(h, minute=0): return h * 60 + minute

    friends = [
        {"name": "Laura", "location": "The Castro", "start": m(19,45), "end": m(21,30), "min": 105},
        {"name": "Daniel", "location": "Golden Gate Park", "start": m(21,15), "end": m(21,45), "min": 15},
        {"name": "William", "location": "Embarcadero", "start": m(7,0), "end": m(9,0), "min": 90},
        {"name": "Karen", "location": "Russian Hill", "start": m(14,30), "end": m(19,45), "min": 30},
        {"name": "Stephanie", "location": "Nob Hill", "start": m(7,30), "end": m(9,30), "min": 45},
        {"name": "Joseph", "location": "Alamo Square", "start": m(11,30), "end": m(12,45), "min": 15},
        {"name": "Kimberly", "location": "North Beach", "start": m(15,45), "end": m(19,15), "min": 30},
    ]

    friends_by_name = {f["name"]: f for f in friends}
    all_names_sorted = tuple(sorted(friends_by_name.keys()))

    start_location = "Fisherman's Wharf"
    start_time = m(9,0)  # 9:00

    def better(sol_a, sol_b):
        # Compare solutions by:
        # 1) more meetings
        # 2) greater total meeting minutes
        # 3) less total travel minutes
        # 4) earlier final end time
        # 5) lexicographically smaller itinerary (stable tie-break)
        a_count = len(sol_a["itinerary"])
        b_count = len(sol_b["itinerary"])
        if a_count != b_count:
            return a_count > b_count
        if sol_a["total_meeting_minutes"] != sol_b["total_meeting_minutes"]:
            return sol_a["total_meeting_minutes"] > sol_b["total_meeting_minutes"]
        if sol_a["total_travel_minutes"] != sol_b["total_travel_minutes"]:
            return sol_a["total_travel_minutes"] < sol_b["total_travel_minutes"]
        if sol_a["end_time"] != sol_b["end_time"]:
            return sol_a["end_time"] < sol_b["end_time"]
        # Final tie-break: itinerary text
        return json.dumps(sol_a["itinerary"]) < json.dumps(sol_b["itinerary"])

    @lru_cache(maxsize=None)
    def dfs(current_loc, current_time, remaining_tuple):
        # Base solution: do nothing from this state
        best = {
            "itinerary": [],
            "total_meeting_minutes": 0,
            "total_travel_minutes": 0,
            "end_time": current_time
        }

        remaining_names = list(remaining_tuple)
        for name in remaining_names:
            f = friends_by_name[name]
            # Travel time; if missing, skip
            if current_loc not in T or f["location"] not in T[current_loc]:
                continue
            travel_mins = T[current_loc][f["location"]]
            arrive = current_time + travel_mins
            start = max(arrive, f["start"])
            end = start + f["min"]
            if end <= f["end"]:
                next_remaining = tuple(sorted([n for n in remaining_names if n != name]))
                sub = dfs(f["location"], end, next_remaining)
                current_meet = {
                    "action": "meet",
                    "location": f["location"],
                    "person": f["name"],
                    "start_time": fmt_time(start),
                    "end_time": fmt_time(end)
                }
                cand = {
                    "itinerary": [current_meet] + sub["itinerary"],
                    "total_meeting_minutes": f["min"] + sub["total_meeting_minutes"],
                    "total_travel_minutes": travel_mins + sub["total_travel_minutes"],
                    "end_time": sub["end_time"]
                }
                if better(cand, best):
                    best = cand

        return best

    best_solution = dfs(start_location, start_time, all_names_sorted)
    print(json.dumps({"itinerary": best_solution["itinerary"]}, indent=2))

if __name__ == "__main__":
    main()