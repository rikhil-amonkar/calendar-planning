# SOLUTION:
import json
import itertools

def time_to_minutes(h, m):
    return h * 60 + m

def fmt_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

# Start parameters
start_location = "Haight-Ashbury"
start_time = time_to_minutes(9, 0)  # 9:00

# Travel times (in minutes), directed as specified
travel = {
    "Haight-Ashbury": {
        "Mission District": 11,
        "Bayview": 18,
        "Pacific Heights": 12,
        "Russian Hill": 17,
        "Fisherman's Wharf": 23,
    },
    "Mission District": {
        "Haight-Ashbury": 12,
        "Bayview": 15,
        "Pacific Heights": 16,
        "Russian Hill": 15,
        "Fisherman's Wharf": 22,
    },
    "Bayview": {
        "Haight-Ashbury": 19,
        "Mission District": 13,
        "Pacific Heights": 23,
        "Russian Hill": 23,
        "Fisherman's Wharf": 25,
    },
    "Pacific Heights": {
        "Haight-Ashbury": 11,
        "Mission District": 15,
        "Bayview": 22,
        "Russian Hill": 7,
        "Fisherman's Wharf": 13,
    },
    "Russian Hill": {
        "Haight-Ashbury": 17,
        "Mission District": 16,
        "Bayview": 23,
        "Pacific Heights": 7,
        "Fisherman's Wharf": 7,
    },
    "Fisherman's Wharf": {
        "Haight-Ashbury": 22,
        "Mission District": 22,
        "Bayview": 26,
        "Pacific Heights": 12,
        "Russian Hill": 7,
    },
}

# Ensure zero travel for staying in place
for a in list(travel.keys()):
    travel[a][a] = 0

# People constraints
friends = {
    "Stephanie": {
        "location": "Mission District",
        "start": time_to_minutes(8, 15),
        "end": time_to_minutes(13, 45),
        "min_duration": 90,
    },
    "Sandra": {
        "location": "Bayview",
        "start": time_to_minutes(13, 0),
        "end": time_to_minutes(19, 30),
        "min_duration": 15,
    },
    "Richard": {
        "location": "Pacific Heights",
        "start": time_to_minutes(7, 15),
        "end": time_to_minutes(10, 15),
        "min_duration": 75,
    },
    "Brian": {
        "location": "Russian Hill",
        "start": time_to_minutes(12, 15),
        "end": time_to_minutes(16, 0),
        "min_duration": 120,
    },
    "Jason": {
        "location": "Fisherman's Wharf",
        "start": time_to_minutes(8, 30),
        "end": time_to_minutes(17, 45),
        "min_duration": 60,
    },
}

def attempt_schedule(order):
    current_loc = start_location
    current_time = start_time
    itinerary = []
    total_travel = 0

    for i, person_name in enumerate(order):
        p = friends[person_name]
        loc = p["location"]
        if current_loc not in travel or loc not in travel[current_loc]:
            return None  # missing travel path
        t_travel = travel[current_loc][loc]
        total_travel += t_travel
        arrival = current_time + t_travel
        start_meet = max(arrival, p["start"])
        end_meet = start_meet + p["min_duration"]
        if end_meet > p["end"]:
            return None  # cannot meet minimum duration

        # If there is a next person, optionally extend this meeting to reduce waiting for next
        if i < len(order) - 1:
            nextp = friends[order[i + 1]]
            next_loc = nextp["location"]
            # Ensure travel path exists
            if loc not in travel or next_loc not in travel[loc]:
                return None
            t_to_next = travel[loc][next_loc]
            arrival_next = end_meet + t_to_next
            earliest_next_start = max(arrival_next, nextp["start"])
            # If we will arrive before next person's window, extend current meeting to reduce waiting
            if arrival_next < nextp["start"]:
                max_extend = min(nextp["start"] - arrival_next, p["end"] - end_meet)
                if max_extend > 0:
                    end_meet += max_extend
                    # recompute arrival_next (should align with nextp["start"] or still before it)
                    arrival_next = end_meet + t_to_next
                    earliest_next_start = max(arrival_next, nextp["start"])

            # Also ensure that even if we extended, we can still meet next person for minimum duration
            # This check will be enforced when we process the next person in loop.
            # No action needed here beyond feasibility of current meeting.

        itinerary.append({
            "action": "meet",
            "location": loc,
            "person": person_name,
            "start_time": fmt_time(start_meet),
            "end_time": fmt_time(end_meet),
        })
        current_loc = loc
        current_time = end_meet

    return {
        "itinerary": itinerary,
        "finish_time": current_time,
        "total_travel": total_travel,
        "count": len(order),
    }

def compute_optimal_itinerary():
    names = list(friends.keys())
    best = None

    # Search by decreasing number of people to maximize count first
    for k in range(len(names), 0, -1):
        feasible_found_for_k = []
        for subset in itertools.combinations(names, k):
            for perm in itertools.permutations(subset):
                result = attempt_schedule(perm)
                if result is not None:
                    feasible_found_for_k.append(result)

        if feasible_found_for_k:
            # Choose the best by earliest finish time, then minimal total travel
            feasible_found_for_k.sort(key=lambda r: (r["finish_time"], r["total_travel"]))
            best = feasible_found_for_k[0]
            break

    if best is None:
        return {"itinerary": []}
    else:
        return {"itinerary": best["itinerary"]}

def main():
    optimal = compute_optimal_itinerary()
    print(json.dumps(optimal, ensure_ascii=False))

if __name__ == "__main__":
    main()