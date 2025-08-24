"SOLUTION:"

import json
from itertools import product

def parse_time(tstr):
    # tstr like '9:00' or '16:30'
    h, m = map(int, tstr.split(':'))
    return h * 60 + m

def fmt_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

def add_travel(times, a, b, minutes):
    times.setdefault(a, {})[b] = minutes

def compute_itineraries():
    # Input variables (constraints and travel times)
    start_location = "North Beach"
    start_time_str = "9:00"
    start_time = parse_time(start_time_str)

    # Travel times (minutes), asymmetric
    travel = {}
    add_travel(travel, "North Beach", "Union Square", 7)
    add_travel(travel, "North Beach", "Russian Hill", 4)
    add_travel(travel, "Union Square", "North Beach", 10)
    add_travel(travel, "Union Square", "Russian Hill", 13)
    add_travel(travel, "Russian Hill", "North Beach", 5)
    add_travel(travel, "Russian Hill", "Union Square", 11)

    # Friends constraints
    friends = {
        "Emily": {
            "location": "Union Square",
            "avail_start": parse_time("16:00"),
            "avail_end": parse_time("17:15"),
            "min_minutes": 45
        },
        "Margaret": {
            "location": "Russian Hill",
            "avail_start": parse_time("19:00"),
            "avail_end": parse_time("21:00"),
            "min_minutes": 120
        }
    }

    # Search parameters
    step = 5  # minutes granularity

    candidates = []

    # Enumerate feasible meeting windows for Emily
    E = friends["Emily"]
    M = friends["Margaret"]

    # Ensure we can reach Emily from start
    travel_start_to_E = travel[start_location][E["location"]]
    earliest_arrive_E = start_time + travel_start_to_E

    # Loop over Emily's possible start times and durations
    latest_start_E = E["avail_end"] - E["min_minutes"]
    for em_start in range(max(E["avail_start"], earliest_arrive_E), latest_start_E + 1, step):
        max_duration_E = E["avail_end"] - em_start
        for em_dur in range(E["min_minutes"], max_duration_E + 1, step):
            em_end = em_start + em_dur

            # After Emily, travel to Margaret
            travel_E_to_M = travel[E["location"]][M["location"]]
            arrive_M = em_end + travel_E_to_M
            mar_start = max(M["avail_start"], arrive_M)
            if mar_start + M["min_minutes"] <= M["avail_end"]:
                # Margaret can be met
                mar_dur = min(M["avail_end"] - mar_start, M["min_minutes"])  # exactly 120 here
                mar_end = mar_start + mar_dur

                total_travel = travel_start_to_E + travel_E_to_M
                total_meet = em_dur + mar_dur
                # Idle time from day start to end of last meeting (not counting meeting+travel)
                span = mar_end - start_time
                idle = span - (total_travel + total_meet)

                candidates.append({
                    "meetings": [
                        {"person": "Emily", "location": E["location"], "start": em_start, "end": em_end, "dur": em_dur},
                        {"person": "Margaret", "location": M["location"], "start": mar_start, "end": mar_end, "dur": mar_dur}
                    ],
                    "metrics": {
                        "count": 2,
                        "total_meeting_minutes": total_meet,
                        "total_travel_minutes": total_travel,
                        "idle_minutes": idle,
                        "last_end": mar_end
                    }
                })

    # If no two-person schedule found, try single-person schedules (fallback)
    if not candidates:
        single_candidates = []

        # Emily only
        for em_start in range(max(E["avail_start"], earliest_arrive_E), latest_start_E + 1, step):
            max_duration_E = E["avail_end"] - em_start
            for em_dur in range(E["min_minutes"], max_duration_E + 1, step):
                em_end = em_start + em_dur
                total_travel = travel_start_to_E
                total_meet = em_dur
                span = em_end - start_time
                idle = span - (total_travel + total_meet)
                single_candidates.append({
                    "meetings": [
                        {"person": "Emily", "location": E["location"], "start": em_start, "end": em_end, "dur": em_dur}
                    ],
                    "metrics": {
                        "count": 1,
                        "total_meeting_minutes": total_meet,
                        "total_travel_minutes": total_travel,
                        "idle_minutes": idle,
                        "last_end": em_end
                    }
                })

        # Margaret only
        travel_start_to_M = travel[start_location][M["location"]]
        arrive_M_earliest = start_time + travel_start_to_M
        mar_start = max(M["avail_start"], arrive_M_earliest)
        if mar_start + M["min_minutes"] <= M["avail_end"]:
            mar_end = mar_start + M["min_minutes"]
            total_travel = travel_start_to_M
            total_meet = M["min_minutes"]
            span = mar_end - start_time
            idle = span - (total_travel + total_meet)
            single_candidates.append({
                "meetings": [
                    {"person": "Margaret", "location": M["location"], "start": mar_start, "end": mar_end, "dur": total_meet}
                ],
                "metrics": {
                    "count": 1,
                    "total_meeting_minutes": total_meet,
                    "total_travel_minutes": total_travel,
                    "idle_minutes": idle,
                    "last_end": mar_end
                }
            })

        candidates = single_candidates

    # Choose best candidate:
    # - maximize number of friends met
    # - then maximize total meeting minutes
    # - then minimize idle time
    # - then earliest last_end
    def sort_key(c):
        m = c["metrics"]
        return (-m["count"], -m["total_meeting_minutes"], m["idle_minutes"], m["last_end"])

    if not candidates:
        return []

    best = sorted(candidates, key=sort_key)[0]
    meetings = best["meetings"]
    itinerary = []
    for mt in meetings:
        itinerary.append({
            "action": "meet",
            "location": mt["location"],
            "person": mt["person"],
            "start_time": fmt_time(mt["start"]),
            "end_time": fmt_time(mt["end"])
        })
    return itinerary

def main():
    itinerary = compute_itineraries()
    output = {"itinerary": itinerary}
    print(json.dumps(output, ensure_ascii=False))

if __name__ == "__main__":
    main()