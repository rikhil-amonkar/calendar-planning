import itertools
import json

def minutes(h, m):
    return h * 60 + m

def time_to_str(mins):
    h = mins // 60
    m = mins % 60
    return f"{h}:{m:02d}"

def compute_best_schedule():
    # Locations
    BAYVIEW = "Bayview"
    RUSSIAN = "Russian Hill"
    ALAMO = "Alamo Square"
    NORTH = "North Beach"
    FINANCIAL = "Financial District"

    # Travel times in minutes (directed)
    travel = {
        BAYVIEW: {
            RUSSIAN: 23,
            ALAMO: 16,
            NORTH: 21,
            FINANCIAL: 19,
        },
        RUSSIAN: {
            BAYVIEW: 23,
            ALAMO: 15,
            NORTH: 5,
            FINANCIAL: 11,
        },
        ALAMO: {
            BAYVIEW: 16,
            RUSSIAN: 13,
            NORTH: 15,
            FINANCIAL: 17,
        },
        NORTH: {
            BAYVIEW: 22,
            RUSSIAN: 4,
            ALAMO: 16,
            FINANCIAL: 8,
        },
        FINANCIAL: {
            BAYVIEW: 19,
            RUSSIAN: 10,
            ALAMO: 17,
            NORTH: 7,
        },
    }

    # Participants with constraints
    people = [
        {
            "name": "Joseph",
            "location": RUSSIAN,
            "avail_start": minutes(8, 30),
            "avail_end": minutes(19, 15),
            "min_duration": 60,
        },
        {
            "name": "Nancy",
            "location": ALAMO,
            "avail_start": minutes(11, 0),
            "avail_end": minutes(16, 0),
            "min_duration": 90,
        },
        {
            "name": "Jason",
            "location": NORTH,
            "avail_start": minutes(16, 45),
            "avail_end": minutes(21, 45),
            "min_duration": 15,
        },
        {
            "name": "Jeffrey",
            "location": FINANCIAL,
            "avail_start": minutes(10, 30),
            "avail_end": minutes(15, 45),
            "min_duration": 45,
        },
    ]

    start_location = BAYVIEW
    start_time = minutes(9, 0)

    def simulate(order):
        current_loc = start_location
        current_time = start_time
        travel_total = 0
        wait_total = 0
        itinerary = []

        for person in order:
            loc = person["location"]
            t = travel[current_loc][loc]
            travel_total += t
            arrival = current_time + t
            start_meet = max(arrival, person["avail_start"])
            end_meet = start_meet + person["min_duration"]
            if end_meet > person["avail_end"]:
                return None  # infeasible
            wait_total += max(0, start_meet - arrival)
            itinerary.append({
                "action": "meet",
                "location": loc,
                "person": person["name"],
                "start_time_mins": start_meet,
                "end_time_mins": end_meet
            })
            current_loc = loc
            current_time = end_meet

        finish_time = current_time
        return {
            "itinerary": itinerary,
            "count": len(order),
            "finish_time": finish_time,
            "travel_total": travel_total,
            "wait_total": wait_total
        }

    best = None

    # Objective priority:
    # 1) Maximize count of meetings
    # 2) Minimize finish time (earliest end)
    # 3) Minimize total travel time
    # 4) Minimize total waiting time
    for r in range(len(people), 0, -1):
        for subset in itertools.combinations(people, r):
            for perm in itertools.permutations(subset):
                result = simulate(perm)
                if result is None:
                    continue
                if best is None:
                    best = result
                else:
                    a = best
                    b = result
                    better = False
                    if b["count"] > a["count"]:
                        better = True
                    elif b["count"] == a["count"]:
                        if b["finish_time"] < a["finish_time"]:
                            better = True
                        elif b["finish_time"] == a["finish_time"]:
                            if b["travel_total"] < a["travel_total"]:
                                better = True
                            elif b["travel_total"] == a["travel_total"]:
                                if b["wait_total"] < a["wait_total"]:
                                    better = True
                    if better:
                        best = b

        if best is not None and best["count"] == len(people):
            # Can't do better than meeting everyone
            break

    # Format final output
    output_itinerary = []
    for item in best["itinerary"]:
        output_itinerary.append({
            "action": "meet",
            "location": item["location"],
            "person": item["person"],
            "start_time": time_to_str(item["start_time_mins"]),
            "end_time": time_to_str(item["end_time_mins"])
        })

    return {"itinerary": output_itinerary}

if __name__ == "__main__":
    plan = compute_best_schedule()
    print(json.dumps(plan, ensure_ascii=False))