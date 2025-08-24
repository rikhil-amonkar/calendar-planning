# SOLUTION:
import json
from itertools import permutations

def to_minutes(h, m):
    return h * 60 + m

def time_str(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

def compute_best_schedule():
    # Locations
    RICHMOND = "Richmond District"
    PAC_HEIGHTS = "Pacific Heights"
    MARINA = "Marina District"

    # Travel times in minutes (directional)
    travel = {
        (RICHMOND, PAC_HEIGHTS): 10,
        (RICHMOND, MARINA): 9,
        (PAC_HEIGHTS, RICHMOND): 12,
        (PAC_HEIGHTS, MARINA): 6,
        (MARINA, RICHMOND): 11,
        (MARINA, PAC_HEIGHTS): 7,
    }

    # Start conditions
    start_location = RICHMOND
    start_time = to_minutes(9, 0)  # 9:00

    # People constraints
    people = {
        "Jessica": {
            "location": PAC_HEIGHTS,
            "avail_start": to_minutes(15, 30),
            "avail_end": to_minutes(16, 45),
            "min_duration": 45,
        },
        "Carol": {
            "location": MARINA,
            "avail_start": to_minutes(11, 30),
            "avail_end": to_minutes(15, 0),
            "min_duration": 60,
        },
    }

    names = list(people.keys())

    # Objective: maximize number of meetings; then minimize total waiting; then earliest finish; then earliest start
    best_plan = None

    # Try meeting all friends first; if not possible, try smaller subsets
    for k in range(len(names), 0, -1):
        found_any = False
        for order in permutations(names, k):
            # We will plan fixed minimum durations for simplicity and to meet constraints optimally
            # Iterate over possible start times for the first meeting minute-by-minute within feasibility
            first = order[0]
            first_info = people[first]
            loc1 = first_info["location"]
            dur1 = first_info["min_duration"]
            avail1_s = first_info["avail_start"]
            avail1_e = first_info["avail_end"]

            # Earliest we can start meeting 1 given we can depart at or after start_time
            t_travel0_1 = travel[(start_location, loc1)]
            earliest_start1 = max(avail1_s, start_time + t_travel0_1)
            latest_start1 = avail1_e - dur1

            if earliest_start1 > latest_start1:
                # No feasible start for first meeting; skip this order
                continue

            # We will consider possible start1 times across range
            for start1 in range(earliest_start1, latest_start1 + 1):
                end1 = start1 + dur1

                current_location = loc1
                current_time = end1  # after meeting 1

                total_wait = 0
                total_travel = 0

                # Travel from start to first meeting can be timed to avoid waiting; no waiting needed at origin
                # Add actual travel time (for tie-breaking if needed)
                total_travel += t_travel0_1

                itinerary = [{
                    "action": "meet",
                    "location": loc1,
                    "person": first,
                    "start_time": time_str(start1),
                    "end_time": time_str(end1),
                }]

                feasible = True

                # Schedule remaining meetings in the chosen order greedily at the earliest feasible times
                prev_location = current_location
                prev_time = current_time

                for idx in range(1, len(order)):
                    name = order[idx]
                    info = people[name]
                    loc = info["location"]
                    dur = info["min_duration"]
                    avail_s = info["avail_start"]
                    avail_e = info["avail_end"]

                    t_travel = travel[(prev_location, loc)]
                    arrive_time = prev_time + t_travel
                    # Earliest we can start this meeting considering availability and travel
                    start_m = max(avail_s, arrive_time)
                    end_m = start_m + dur
                    if end_m > avail_e:
                        feasible = False
                        break

                    # Waiting time if we arrived before availability
                    wait = max(0, start_m - arrive_time)
                    total_wait += wait
                    total_travel += t_travel

                    itinerary.append({
                        "action": "meet",
                        "location": loc,
                        "person": name,
                        "start_time": time_str(start_m),
                        "end_time": time_str(end_m),
                    })

                    prev_location = loc
                    prev_time = end_m

                if not feasible:
                    continue

                found_any = True

                # Metrics for tie-breaking
                num_meetings = len(order)
                finish_time = prev_time
                first_meet_start = start1

                candidate = {
                    "num_meetings": num_meetings,
                    "total_wait": total_wait,
                    "finish_time": finish_time,
                    "first_start": first_meet_start,
                    "total_travel": total_travel,
                    "itinerary": itinerary,
                }

                def is_better(a, b):
                    if b is None:
                        return True
                    # Primary: more meetings
                    if a["num_meetings"] != b["num_meetings"]:
                        return a["num_meetings"] > b["num_meetings"]
                    # Secondary: less waiting
                    if a["total_wait"] != b["total_wait"]:
                        return a["total_wait"] < b["total_wait"]
                    # Tertiary: earlier finish
                    if a["finish_time"] != b["finish_time"]:
                        return a["finish_time"] < b["finish_time"]
                    # Next: less travel
                    if a["total_travel"] != b["total_travel"]:
                        return a["total_travel"] < b["total_travel"]
                    # Final: earlier first meeting start
                    return a["first_start"] < b["first_start"]

                if is_better(candidate, best_plan):
                    best_plan = candidate

        if found_any:
            break  # we found at least one plan with k meetings; no need to try fewer

    # Prepare JSON output
    output = {
        "itinerary": best_plan["itinerary"] if best_plan else []
    }
    return output

if __name__ == "__main__":
    result = compute_best_schedule()
    print(json.dumps(result, ensure_ascii=False))