import json
from itertools import permutations

def minutes(h, m):
    return h * 60 + m

def minutes_to_str(t):
    h = t // 60
    m = t % 60
    return f"{h}:{m:02d}"

def build_travel_times():
    FW = "Fisherman's Wharf"
    BV = "Bayview"
    GGP = "Golden Gate Park"
    NH = "Nob Hill"
    MD = "Marina District"
    EMB = "Embarcadero"

    travel = {}
    def set_time(a, b, t):
        travel[(a, b)] = t

    # Fisherman's Wharf to ...
    set_time(FW, BV, 26)
    set_time(FW, GGP, 25)
    set_time(FW, NH, 11)
    set_time(FW, MD, 9)
    set_time(FW, EMB, 8)

    # Bayview to ...
    set_time(BV, FW, 25)
    set_time(BV, GGP, 22)
    set_time(BV, NH, 20)
    set_time(BV, MD, 25)
    set_time(BV, EMB, 19)

    # Golden Gate Park to ...
    set_time(GGP, FW, 24)
    set_time(GGP, BV, 23)
    set_time(GGP, NH, 20)
    set_time(GGP, MD, 16)
    set_time(GGP, EMB, 25)

    # Nob Hill to ...
    set_time(NH, FW, 11)
    set_time(NH, BV, 19)
    set_time(NH, GGP, 17)
    set_time(NH, MD, 11)
    set_time(NH, EMB, 9)

    # Marina District to ...
    set_time(MD, FW, 10)
    set_time(MD, BV, 27)
    set_time(MD, GGP, 18)
    set_time(MD, NH, 12)
    set_time(MD, EMB, 14)

    # Embarcadero to ...
    set_time(EMB, FW, 6)
    set_time(EMB, BV, 21)
    set_time(EMB, GGP, 25)
    set_time(EMB, NH, 10)
    set_time(EMB, MD, 12)

    # zero self-travel
    for loc in [FW, BV, GGP, NH, MD, EMB]:
        travel[(loc, loc)] = 0

    return travel

def build_people():
    return [
        {
            "person": "Thomas",
            "location": "Bayview",
            "avail_start": minutes(15, 30),
            "avail_end": minutes(18, 30),
            "min_duration": 120
        },
        {
            "person": "Stephanie",
            "location": "Golden Gate Park",
            "avail_start": minutes(18, 30),
            "avail_end": minutes(21, 45),
            "min_duration": 30
        },
        {
            "person": "Laura",
            "location": "Nob Hill",
            "avail_start": minutes(8, 45),
            "avail_end": minutes(16, 15),
            "min_duration": 30
        },
        {
            "person": "Betty",
            "location": "Marina District",
            "avail_start": minutes(18, 45),
            "avail_end": minutes(21, 45),
            "min_duration": 45
        },
        {
            "person": "Patricia",
            "location": "Embarcadero",
            "avail_start": minutes(17, 30),
            "avail_end": minutes(22, 0),
            "min_duration": 45
        }
    ]

def try_extend_schedule(order, travel, start_loc, start_time):
    current_loc = start_loc
    current_time = start_time
    itinerary = []
    total_travel = 0

    for friend in order:
        loc = friend["location"]
        t_travel = travel[(current_loc, loc)]
        arrive = current_time + t_travel

        latest_start = friend["avail_end"] - friend["min_duration"]
        if arrive > latest_start:
            # can't meet this friend in this order
            return None

        meet_start = max(arrive, friend["avail_start"])
        meet_end = meet_start + friend["min_duration"]
        if meet_end > friend["avail_end"]:
            return None

        itinerary.append({
            "action": "meet",
            "location": loc,
            "person": friend["person"],
            "start_min": meet_start,
            "end_min": meet_end,
            "travel_in_min": t_travel
        })
        current_loc = loc
        current_time = meet_end
        total_travel += t_travel

    return {
        "itinerary": itinerary,
        "end_time": current_time,
        "total_travel": total_travel
    }

def search_best_schedule(people, travel, start_loc, start_time):
    # Primary: maximize number of friends met
    # Secondary: minimize end time
    # Tertiary: minimize total travel time
    best = None

    n = len(people)
    # Explore all subset sizes from n down to 1
    for k in range(n, 0, -1):
        best_for_k = None
        for order in permutations(people, k):
            plan = try_extend_schedule(order, travel, start_loc, start_time)
            if plan is None:
                # Even if this full k-order fails, some subsequence might work,
                # but we'll consider that when we iterate smaller k.
                continue
            # Evaluate
            end_time = plan["end_time"]
            total_travel = plan["total_travel"]
            if best_for_k is None:
                best_for_k = (end_time, total_travel, plan)
            else:
                be, bt, _ = best_for_k
                if end_time < be or (end_time == be and total_travel < bt):
                    best_for_k = (end_time, total_travel, plan)
        if best_for_k is not None:
            # Found at least one feasible plan of size k; that's optimal in count
            best = best_for_k[2]
            break

    return best

def format_output(plan):
    out_itin = []
    if plan is None:
        # No meetings possible; return empty itinerary
        pass
    else:
        for step in plan["itinerary"]:
            out_itin.append({
                "action": "meet",
                "location": step["location"],
                "person": step["person"],
                "start_time": minutes_to_str(step["start_min"]),
                "end_time": minutes_to_str(step["end_min"])
            })
    return {"itinerary": out_itin}

def main():
    # Inputs
    start_location = "Fisherman's Wharf"
    arrival_time = minutes(9, 0)

    travel = build_travel_times()
    people = build_people()

    # Compute optimal schedule
    best_plan = search_best_schedule(people, travel, start_location, arrival_time)

    # Output JSON
    result = format_output(best_plan)
    print(json.dumps(result, ensure_ascii=False))

if __name__ == "__main__":
    main()