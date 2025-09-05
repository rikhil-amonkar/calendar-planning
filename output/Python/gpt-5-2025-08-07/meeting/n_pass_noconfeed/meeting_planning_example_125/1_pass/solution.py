import json
import itertools

def parse_time_12h(s):
    s = s.strip().upper()
    if not (s.endswith("AM") or s.endswith("PM")):
        raise ValueError(f"Time must end with AM/PM: {s}")
    ampm = s[-2:]
    hm = s[:-2].strip()
    parts = hm.split(":")
    if len(parts) != 2:
        raise ValueError(f"Time must be H:MM format: {s}")
    h = int(parts[0])
    m = int(parts[1])
    if ampm == "AM":
        if h == 12:
            h = 0
    else:
        if h != 12:
            h += 12
    return h * 60 + m

def fmt_time_24h(mins):
    mins = mins % (24 * 60)
    h = mins // 60
    m = mins % 60
    return f"{h}:{m:02d}"

def compute_schedule(order, start_loc, start_time, travel_times):
    itinerary = []
    cur_loc = start_loc
    cur_time = start_time
    total_travel = 0

    for person in order:
        loc = person["location"]
        travel = travel_times[(cur_loc, loc)]
        arrival = cur_time + travel
        total_travel += travel

        start_meet = max(arrival, person["avail_start"])
        end_meet = start_meet + person["min_duration"]

        if end_meet > person["avail_end"]:
            return None  # infeasible

        itinerary.append({
            "action": "meet",
            "location": loc,
            "person": person["name"],
            "start_time": fmt_time_24h(start_meet),
            "end_time": fmt_time_24h(end_meet),
        })

        cur_loc = loc
        cur_time = end_meet

    return {
        "itinerary": itinerary,
        "final_time": cur_time,
        "total_travel": total_travel,
        "met_count": len(itinerary),
    }

def better(plan_a, plan_b):
    # Return True if plan_a is better than plan_b
    if plan_b is None:
        return True
    # Primary: maximize number of friends met
    if plan_a["met_count"] != plan_b["met_count"]:
        return plan_a["met_count"] > plan_b["met_count"]
    # Secondary: earliest final end time
    if plan_a["final_time"] != plan_b["final_time"]:
        return plan_a["final_time"] < plan_b["final_time"]
    # Tertiary: minimal total travel time
    if plan_a["total_travel"] != plan_b["total_travel"]:
        return plan_a["total_travel"] < plan_b["total_travel"]
    # Quaternary: lexicographically smaller itinerary (deterministic tie-breaker)
    return json.dumps(plan_a["itinerary"]) < json.dumps(plan_b["itinerary"])

def main():
    # Input variables (constraints)
    start_location = "Embarcadero"
    arrival_time_str = "9:00AM"

    participants = [
        {
            "name": "Stephanie",
            "location": "Financial District",
            "avail_start_str": "8:15AM",
            "avail_end_str": "11:30AM",
            "min_duration": 90,  # minutes
        },
        {
            "name": "John",
            "location": "Alamo Square",
            "avail_start_str": "10:15AM",
            "avail_end_str": "8:45PM",
            "min_duration": 30,  # minutes
        },
    ]

    # Travel times (in minutes)
    travel_times = {
        ("Embarcadero", "Financial District"): 5,
        ("Embarcadero", "Alamo Square"): 19,
        ("Financial District", "Embarcadero"): 4,
        ("Financial District", "Alamo Square"): 17,
        ("Alamo Square", "Embarcadero"): 17,
        ("Alamo Square", "Financial District"): 17,
    }

    # Parse times
    start_time = parse_time_12h(arrival_time_str)
    for p in participants:
        p["avail_start"] = parse_time_12h(p["avail_start_str"])
        p["avail_end"] = parse_time_12h(p["avail_end_str"])

    # Enumerate schedules: try to meet as many friends as possible
    n = len(participants)
    best_plan = None

    for r in range(n, 0, -1):
        # Consider all permutations of r participants
        for order in itertools.permutations(participants, r):
            plan = compute_schedule(order, start_location, start_time, travel_times)
            if plan is not None and better(plan, best_plan):
                best_plan = plan
        if best_plan is not None and best_plan["met_count"] == r:
            # Found the best possible count; no need to consider smaller r
            break

    # Prepare output
    output = {"itinerary": []}
    if best_plan is not None:
        output["itinerary"] = best_plan["itinerary"]

    print(json.dumps(output))

if __name__ == "__main__":
    main()