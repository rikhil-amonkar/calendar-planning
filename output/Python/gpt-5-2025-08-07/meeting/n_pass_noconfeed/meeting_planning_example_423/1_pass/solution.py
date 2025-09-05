# SOLUTION:
import json
from itertools import combinations, permutations

def time_to_minutes(hhmm):
    h, m = map(int, hhmm.split(":"))
    return h * 60 + m

def minutes_to_time(m):
    h = m // 60
    mm = m % 60
    return f"{h}:{mm:02d}"

# Travel times in minutes (directed)
travel = {
    "Presidio": {
        "Richmond District": 7,
        "North Beach": 18,
        "Financial District": 23,
        "Golden Gate Park": 12,
        "Union Square": 22,
    },
    "Richmond District": {
        "Presidio": 7,
        "North Beach": 17,
        "Financial District": 22,
        "Golden Gate Park": 9,
        "Union Square": 21,
    },
    "North Beach": {
        "Presidio": 17,
        "Richmond District": 18,
        "Financial District": 8,
        "Golden Gate Park": 22,
        "Union Square": 7,
    },
    "Financial District": {
        "Presidio": 22,
        "Richmond District": 21,
        "North Beach": 7,
        "Golden Gate Park": 23,
        "Union Square": 9,
    },
    "Golden Gate Park": {
        "Presidio": 11,
        "Richmond District": 7,
        "North Beach": 24,
        "Financial District": 26,
        "Union Square": 22,
    },
    "Union Square": {
        "Presidio": 24,
        "Richmond District": 20,
        "North Beach": 10,
        "Financial District": 9,
        "Golden Gate Park": 22,
    },
}

# Input variables for meeting constraints
start_location = "Presidio"
start_time = time_to_minutes("9:00")

people = {
    "Jason": {
        "location": "Richmond District",
        "start": time_to_minutes("13:00"),
        "end": time_to_minutes("20:45"),
        "min_duration": 90,
    },
    "Melissa": {
        "location": "North Beach",
        "start": time_to_minutes("18:45"),
        "end": time_to_minutes("20:15"),
        "min_duration": 45,
    },
    "Brian": {
        "location": "Financial District",
        "start": time_to_minutes("9:45"),
        "end": time_to_minutes("21:45"),
        "min_duration": 15,
    },
    "Elizabeth": {
        "location": "Golden Gate Park",
        "start": time_to_minutes("8:45"),
        "end": time_to_minutes("21:30"),
        "min_duration": 105,
    },
    "Laura": {
        "location": "Union Square",
        "start": time_to_minutes("14:15"),
        "end": time_to_minutes("19:30"),
        "min_duration": 75,
    },
}

def try_schedule(order):
    current_loc = start_location
    current_time = start_time
    itinerary = []
    total_wait = 0
    total_travel = 0

    for person in order:
        loc = people[person]["location"]

        # Travel
        if current_loc == loc:
            travel_time = 0
        else:
            if current_loc not in travel or loc not in travel[current_loc]:
                return None  # no travel path defined
            travel_time = travel[current_loc][loc]
        current_time += travel_time
        total_travel += travel_time

        # Wait if early
        avail_start = people[person]["start"]
        avail_end = people[person]["end"]
        if current_time < avail_start:
            total_wait += (avail_start - current_time)
            current_time = avail_start

        # Meet
        meet_duration = people[person]["min_duration"]
        meet_end = current_time + meet_duration
        if meet_end > avail_end:
            return None  # cannot meet within window

        itinerary.append({
            "action": "meet",
            "location": loc,
            "person": person,
            "start_time": minutes_to_time(current_time),
            "end_time": minutes_to_time(meet_end),
        })

        # Update state
        current_time = meet_end
        current_loc = loc

    return {
        "itinerary": itinerary,
        "finish_time": current_time,
        "total_wait": total_wait,
        "total_travel": total_travel,
        "met_count": len(order),
    }

def optimize_schedule():
    names = list(people.keys())
    best_solution = None

    # Optimize: maximize number met, then minimize finish time, then total wait, then total travel
    for k in range(len(names), 0, -1):
        found_any = False
        best_k = None
        for subset in combinations(names, k):
            for order in permutations(subset):
                res = try_schedule(order)
                if res is None:
                    continue
                found_any = True
                if best_k is None:
                    best_k = res
                else:
                    # Compare tie-breakers: earliest finish, then least wait, then least travel
                    a = (best_k["finish_time"], best_k["total_wait"], best_k["total_travel"])
                    b = (res["finish_time"], res["total_wait"], res["total_travel"])
                    if b < a:
                        best_k = res
        if found_any:
            best_solution = best_k
            break

    return best_solution

def main():
    solution = optimize_schedule()
    output = {"itinerary": solution["itinerary"] if solution else []}
    print(json.dumps(output, ensure_ascii=False))

if __name__ == "__main__":
    main()