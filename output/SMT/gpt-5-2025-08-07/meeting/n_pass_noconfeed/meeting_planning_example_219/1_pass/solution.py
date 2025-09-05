import json
from itertools import permutations, combinations
from z3 import Optimize, Int, Sum, sat

# Helper to format minutes since midnight into 'H:MM' 24-hour format (no leading zero for hour)
def fmt_time(m):
    h = m // 60
    mi = m % 60
    return f"{h}:{mi:02d}"

def build_and_solve_for_order(order, people, travel, start_location, arrival_time):
    """
    Build an SMT model for a fixed meeting order and solve to maximize total meeting duration.
    Returns (is_feasible, itinerary, total_minutes).
    """
    K = len(order)
    opt = Optimize()

    # Time variables for each meeting in the order
    starts = [Int(f"start_{i}") for i in range(K)]
    ends = [Int(f"end_{i}") for i in range(K)]

    # Constraints for each meeting
    for i, person in enumerate(order):
        w_start = people[person]["window_start"]
        w_end = people[person]["window_end"]
        min_dur = people[person]["min_duration"]
        loc = people[person]["location"]

        # Meeting within person's availability window and meeting duration
        opt.add(starts[i] >= w_start)
        opt.add(ends[i] <= w_end)
        opt.add(ends[i] - starts[i] >= min_dur)
        opt.add(starts[i] < ends[i])

        # Travel-time constraints from previous point
        if i == 0:
            # From starting location at arrival_time
            ttime = travel[(start_location, loc)]
            opt.add(starts[i] >= arrival_time + ttime)
        else:
            prev_loc = people[order[i - 1]]["location"]
            ttime = travel[(prev_loc, loc)]
            opt.add(starts[i] >= ends[i - 1] + ttime)

    # Objective: maximize total meeting time (sum of meeting durations)
    total_meeting_time = Sum([ends[i] - starts[i] for i in range(K)])
    opt.maximize(total_meeting_time)

    if opt.check() == sat:
        model = opt.model()
        itinerary = []
        total_minutes = 0
        for i, person in enumerate(order):
            loc = people[person]["location"]
            s = model[starts[i]].as_long()
            e = model[ends[i]].as_long()
            total_minutes += (e - s)
            itinerary.append({
                "action": "meet",
                "location": loc,
                "person": person,
                "start_time": fmt_time(s),
                "end_time": fmt_time(e)
            })
        return True, itinerary, total_minutes
    else:
        return False, [], 0

def main():
    # Locations and travel times (in minutes)
    Castro = "The Castro"
    Alamo = "Alamo Square"
    Union = "Union Square"
    China = "Chinatown"

    travel = {
        (Castro, Alamo): 8,
        (Castro, Union): 19,
        (Castro, China): 20,

        (Alamo, Castro): 8,
        (Alamo, Union): 14,
        (Alamo, China): 16,

        (Union, Castro): 19,
        (Union, Alamo): 15,
        (Union, China): 7,

        (China, Castro): 22,
        (China, Alamo): 17,
        (China, Union): 7,
    }

    # People, locations, availability windows, and required minimum meeting durations
    # Times are minutes since midnight
    def mins(h, m): return h * 60 + m

    people = {
        "Emily": {
            "location": Alamo,
            "window_start": mins(11, 45),
            "window_end": mins(15, 15),
            "min_duration": 105
        },
        "Barbara": {
            "location": Union,
            "window_start": mins(16, 45),
            "window_end": mins(18, 15),
            "min_duration": 60
        },
        "William": {
            "location": China,
            "window_start": mins(17, 15),
            "window_end": mins(19, 0),
            "min_duration": 105
        }
    }

    # Start at The Castro at 9:00
    start_location = Castro
    arrival_time = mins(9, 0)

    names = list(people.keys())

    best_itinerary = []
    best_count = -1
    best_total_minutes = -1

    # Consider all non-empty subsets and all permutations (orders) for each subset
    for r in range(1, len(names) + 1):
        for subset in combinations(names, r):
            for order in permutations(subset):
                feasible, itinerary, total_minutes = build_and_solve_for_order(order, people, travel, start_location, arrival_time)
                if feasible:
                    count = len(itinerary)
                    # Primary objective: meet as many friends as possible
                    # Secondary objective: maximize total meeting minutes
                    if count > best_count or (count == best_count and total_minutes > best_total_minutes):
                        best_count = count
                        best_total_minutes = total_minutes
                        best_itinerary = itinerary

    result = {
        "itinerary": best_itinerary
    }

    print(json.dumps(result, ensure_ascii=False))

if __name__ == "__main__":
    main()