import itertools
import json

# Utility functions
def t2min(t):
    h, m = map(int, t.split(":"))
    return h * 60 + m

def min2t(m):
    h = m // 60
    mm = m % 60
    return f"{h}:{mm:02d}"

# Input variables (constraints and travel times)
start_location = "Fisherman's Wharf"
start_time = t2min("9:00")

travel = {
    ("Fisherman's Wharf", "Golden Gate Park"): 25,
    ("Fisherman's Wharf", "Presidio"): 17,
    ("Fisherman's Wharf", "Richmond District"): 18,
    ("Golden Gate Park", "Fisherman's Wharf"): 24,
    ("Golden Gate Park", "Presidio"): 11,
    ("Golden Gate Park", "Richmond District"): 7,
    ("Presidio", "Fisherman's Wharf"): 19,
    ("Presidio", "Golden Gate Park"): 12,
    ("Presidio", "Richmond District"): 7,
    ("Richmond District", "Fisherman's Wharf"): 18,
    ("Richmond District", "Golden Gate Park"): 9,
    ("Richmond District", "Presidio"): 7,
}

people = {
    "Melissa": {
        "location": "Golden Gate Park",
        "start": t2min("8:30"),
        "end": t2min("20:00"),
        "min_duration": 15
    },
    "Nancy": {
        "location": "Presidio",
        "start": t2min("19:45"),
        "end": t2min("22:00"),
        "min_duration": 105
    },
    "Emily": {
        "location": "Richmond District",
        "start": t2min("16:45"),
        "end": t2min("22:00"),
        "min_duration": 120
    }
}

# Planning algorithm: enumerate schedules to maximize number of friends met,
# then minimize end time, then minimize total travel time, then minimize waiting.
def evaluate_order(order):
    current_loc = start_location
    current_time = start_time
    itinerary = []
    total_travel = 0
    total_wait = 0

    for name in order:
        person = people[name]
        dest = person["location"]
        if (current_loc, dest) not in travel:
            return None  # invalid route

        # Travel to destination
        travel_time = travel[(current_loc, dest)]
        arrival = current_time + travel_time
        total_travel += travel_time

        # Determine meeting start (may need to wait)
        meet_start = max(arrival, person["start"])
        wait = max(0, meet_start - arrival)
        total_wait += wait

        # Meeting end
        meet_end = meet_start + person["min_duration"]
        if meet_end > person["end"]:
            return None  # cannot meet within window

        itinerary.append({
            "action": "meet",
            "location": dest,
            "person": name,
            "start_time": min2t(meet_start),
            "end_time": min2t(meet_end)
        })

        # Update state
        current_loc = dest
        current_time = meet_end

    return {
        "num_met": len(order),
        "end_time": current_time,
        "total_travel": total_travel,
        "total_wait": total_wait,
        "itinerary": itinerary
    }

def best_schedule():
    names = list(people.keys())
    best = None

    # Consider all non-empty subsets and all permutations of each subset
    for r in range(1, len(names) + 1):
        for subset in itertools.combinations(names, r):
            for perm in itertools.permutations(subset):
                result = evaluate_order(perm)
                if result is None:
                    continue
                # Objective: maximize number met; tie-break by earliest end time,
                # then minimal total travel, then minimal waiting.
                key = (-result["num_met"], result["end_time"], result["total_travel"], result["total_wait"])
                if best is None or key < best["key"]:
                    best = {"key": key, "result": result}

    return best["result"] if best else {"itinerary": []}

def main():
    result = best_schedule()
    output = {"itinerary": result["itinerary"]}
    print(json.dumps(output, ensure_ascii=False))

if __name__ == "__main__":
    main()