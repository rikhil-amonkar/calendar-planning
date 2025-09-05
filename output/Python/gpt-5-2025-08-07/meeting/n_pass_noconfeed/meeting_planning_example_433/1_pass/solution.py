import json
import itertools

def time_to_minutes(t):
    h, m = map(int, t.split(":"))
    return h * 60 + m

def minutes_to_time(m):
    h = m // 60
    mm = m % 60
    return f"{h}:{mm:02d}"

def compute_schedule(order, start_loc, start_time_min, people, travel):
    itinerary = []
    current_loc = start_loc
    current_time = start_time_min
    total_wait = 0
    total_travel = 0
    total_meet = 0

    for name in order:
        person = people[name]
        travel_time = travel[current_loc][person["location"]]
        arrive = current_time + travel_time
        start = max(arrive, person["start"])
        end = start + person["min_duration"]
        if end > person["end"]:
            return None  # infeasible
        wait = max(0, person["start"] - arrive)

        itinerary.append({
            "action": "meet",
            "location": person["location"],
            "person": name,
            "start_time": minutes_to_time(start),
            "end_time": minutes_to_time(end)
        })

        total_wait += wait
        total_travel += travel_time
        total_meet += person["min_duration"]
        current_time = end
        current_loc = person["location"]

    return {
        "itinerary": itinerary,
        "metrics": {
            "num_meetings": len(order),
            "total_meeting_time": total_meet,
            "finish_time": current_time,
            "total_wait": total_wait,
            "total_travel": total_travel
        }
    }

def best_schedule(start_location, start_time, people, travel):
    names = list(people.keys())
    start_time_min = time_to_minutes(start_time)

    best = None
    best_key = None

    # Search by decreasing number of meetings
    for k in range(len(names), 0, -1):
        found_any = False
        for combo in itertools.combinations(names, k):
            for perm in itertools.permutations(combo):
                result = compute_schedule(perm, start_location, start_time_min, people, travel)
                if result is None:
                    continue
                found_any = True
                metrics = result["metrics"]
                # Objective: maximize meetings, then total meeting time, then earliest finish, then minimal wait, then minimal travel
                key = (
                    metrics["num_meetings"],
                    metrics["total_meeting_time"],
                    -metrics["finish_time"],
                    -metrics["total_wait"],
                    -metrics["total_travel"],
                )
                if best is None or key > best_key:
                    best = result
                    best_key = key
        if found_any:
            break  # We have the maximum possible number of meetings
    return best

def main():
    # Input variables (constraints)
    start_location = "Nob Hill"
    start_time = "9:00"

    people = {
        "Emily": {
            "location": "Richmond District",
            "start": time_to_minutes("19:00"),
            "end": time_to_minutes("21:00"),
            "min_duration": 15
        },
        "Margaret": {
            "location": "Financial District",
            "start": time_to_minutes("16:30"),
            "end": time_to_minutes("20:15"),
            "min_duration": 75
        },
        "Ronald": {
            "location": "North Beach",
            "start": time_to_minutes("18:30"),
            "end": time_to_minutes("19:30"),
            "min_duration": 45
        },
        "Deborah": {
            "location": "The Castro",
            "start": time_to_minutes("13:45"),
            "end": time_to_minutes("21:15"),
            "min_duration": 90
        },
        "Jeffrey": {
            "location": "Golden Gate Park",
            "start": time_to_minutes("11:15"),
            "end": time_to_minutes("14:30"),
            "min_duration": 120
        }
    }

    # Directed travel times in minutes
    travel = {
        "Nob Hill": {
            "Richmond District": 14,
            "Financial District": 9,
            "North Beach": 8,
            "The Castro": 17,
            "Golden Gate Park": 17
        },
        "Richmond District": {
            "Nob Hill": 17,
            "Financial District": 22,
            "North Beach": 17,
            "The Castro": 16,
            "Golden Gate Park": 9
        },
        "Financial District": {
            "Nob Hill": 8,
            "Richmond District": 21,
            "North Beach": 7,
            "The Castro": 23,
            "Golden Gate Park": 23
        },
        "North Beach": {
            "Nob Hill": 7,
            "Richmond District": 18,
            "Financial District": 8,
            "The Castro": 22,
            "Golden Gate Park": 22
        },
        "The Castro": {
            "Nob Hill": 16,
            "Richmond District": 16,
            "Financial District": 20,
            "North Beach": 20,
            "Golden Gate Park": 11
        },
        "Golden Gate Park": {
            "Nob Hill": 20,
            "Richmond District": 7,
            "Financial District": 26,
            "North Beach": 24,
            "The Castro": 13
        }
    }

    result = best_schedule(start_location, start_time, people, travel)
    output = {"itinerary": result["itinerary"] if result else []}
    print(json.dumps(output, indent=2))

if __name__ == "__main__":
    main()