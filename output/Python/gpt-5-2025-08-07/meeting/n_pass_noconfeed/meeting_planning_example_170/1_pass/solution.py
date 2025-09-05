import json
from itertools import permutations, product

def to_minutes(t):
    h, m = map(int, t.split(":"))
    return h * 60 + m

def to_time_str(m):
    h = m // 60
    mm = m % 60
    return f"{h}:{mm:02d}"

def travel_time(a, b, travel_map):
    if a == b:
        return 0
    return travel_map.get(a, {}).get(b, float("inf"))

def generate_candidate_intervals(window_start, window_end, min_duration, step=5):
    candidates = []
    window_len = window_end - window_start
    for dur in range(min_duration, window_len + 1, step):
        latest_start = window_end - dur
        start_time = window_start
        while start_time <= latest_start:
            candidates.append((start_time, start_time + dur))
            start_time += step
    return candidates

def compute_best_schedule(start_location, start_time_str, people, travel_map, step=5):
    start_time = to_minutes(start_time_str)

    # Precompute candidate intervals for each person
    person_candidates = {}
    for p in people:
        ws = to_minutes(p["window_start"])
        we = to_minutes(p["window_end"])
        person_candidates[p["name"]] = generate_candidate_intervals(ws, we, p["min_duration"], step)

    best = None  # (score_tuple, itinerary_list)

    # Try schedules meeting maximum number of friends first
    for k in range(len(people), 0, -1):
        for order in permutations(people, k):
            # Build candidate list per person in order
            candidate_lists = [person_candidates[p["name"]] for p in order]
            for combo in product(*candidate_lists):
                # Check feasibility with travel times
                current_loc = start_location
                current_time = start_time
                itinerary = []
                total_meeting = 0
                total_travel = 0
                feasible = True

                for idx, (p, interval) in enumerate(zip(order, combo)):
                    start, end = interval
                    t_travel = travel_time(current_loc, p["location"], travel_map)
                    if start >= current_time + t_travel:
                        # feasible leg
                        total_travel += t_travel
                        itinerary.append({
                            "action": "meet",
                            "location": p["location"],
                            "person": p["name"],
                            "start_time": to_time_str(start),
                            "end_time": to_time_str(end)
                        })
                        total_meeting += (end - start)
                        current_loc = p["location"]
                        current_time = end
                    else:
                        feasible = False
                        break

                if not feasible:
                    continue

                # Compute idle time from start to end of last meeting (excluding travel and meetings)
                day_end = current_time
                idle_time = (day_end - start_time) - (total_meeting + total_travel)
                if idle_time < 0:
                    idle_time = 0  # numerical safety

                # Score: maximize number met, then total meeting time, then minimize idle and travel
                score = (len(order), total_meeting, -idle_time, -total_travel)

                if best is None or score > best[0]:
                    best = (score, itinerary)

        if best is not None and best[0][0] == k:
            # Found best for this k; no need to try fewer people
            break

    return best[1] if best else []

def main():
    # Input variables based on problem statement
    travel_map = {
        "North Beach": {
            "Union Square": 7,
            "Russian Hill": 4
        },
        "Union Square": {
            "North Beach": 10,
            "Russian Hill": 13
        },
        "Russian Hill": {
            "North Beach": 5,
            "Union Square": 11
        }
    }

    start_location = "North Beach"
    start_time = "9:00"

    people = [
        {
            "name": "Emily",
            "location": "Union Square",
            "window_start": "16:00",
            "window_end": "17:15",
            "min_duration": 45
        },
        {
            "name": "Margaret",
            "location": "Russian Hill",
            "window_start": "19:00",
            "window_end": "21:00",
            "min_duration": 120
        }
    ]

    itinerary = compute_best_schedule(start_location, start_time, people, travel_map, step=5)

    output = {
        "itinerary": itinerary
    }
    print(json.dumps(output, ensure_ascii=False))

if __name__ == "__main__":
    main()