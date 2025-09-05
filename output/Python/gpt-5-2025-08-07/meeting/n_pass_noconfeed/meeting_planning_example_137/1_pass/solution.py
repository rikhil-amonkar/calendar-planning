import json
import itertools

def time_to_minutes(t):
    # t in 'H:MM' or 'HH:MM' 24h format
    h, m = map(int, t.split(':'))
    return h * 60 + m

def minutes_to_time(m):
    h = m // 60
    mm = m % 60
    return f"{h}:{mm:02d}"

def compute_schedule(order, start_location, start_time, participants, travel):
    itinerary = []
    current_loc = start_location
    current_time = start_time
    total_wait = 0

    # Precompute a map for quick lookup
    pmap = {p["name"]: p for p in participants}

    for i, name in enumerate(order):
        p = pmap[name]
        # Travel to meeting location
        travel_time = travel.get((current_loc, p["location"]))
        if travel_time is None:
            return None  # invalid route
        arrival = current_time + travel_time

        # Earliest possible start respecting arrival and availability
        start_meet = max(arrival, p["avail_start"])
        # Minimal end time based on minimum duration
        min_end = start_meet + p["min_duration"]
        if min_end > p["avail_end"]:
            return None  # cannot satisfy minimum duration within availability

        # If not the last meeting, consider extending this meeting to reduce waiting for the next
        end_meet = min_end
        if i < len(order) - 1:
            next_p = pmap[order[i + 1]]
            # Travel time to next meeting
            t_to_next = travel.get((p["location"], next_p["location"]))
            if t_to_next is None:
                return None
            # Earliest arrival to next meeting if we end at min_end
            arrive_next = end_meet + t_to_next
            # Earliest feasible start for next meeting
            next_earliest_start = next_p["avail_start"]
            next_latest_start = next_p["avail_end"] - next_p["min_duration"]
            if next_latest_start < next_earliest_start:
                return None  # next meeting impossible regardless

            if arrive_next < next_earliest_start:
                # We would wait for next meeting; extend current meeting if possible to reduce waiting
                # Target to end such that arrival equals next_earliest_start
                target_end = next_earliest_start - t_to_next
                # Ensure we minimally meet with current person
                proposed_end = min(target_end, p["avail_end"])
                if proposed_end < end_meet:
                    proposed_end = end_meet  # cannot reduce below minimal
                # Also ensure that with proposed_end, next meeting still feasible (arrival <= latest start)
                if proposed_end + t_to_next <= next_latest_start:
                    end_meet = proposed_end
                # recompute arrival to next and add any remaining wait later
            else:
                # No waiting needed if we end at min_end; keeping minimal end to finish earlier
                pass

        # Accumulate waiting for this meeting start (if arrival earlier than start)
        if arrival < start_meet:
            total_wait += start_meet - arrival

        itinerary.append({
            "action": "meet",
            "location": p["location"],
            "person": p["name"],
            "start_time": minutes_to_time(start_meet),
            "end_time": minutes_to_time(end_meet),
            "_start_min": start_meet,  # internal for evaluation
            "_end_min": end_meet,      # internal for evaluation
            "_arrival_min": arrival    # internal for evaluation
        })

        current_loc = p["location"]
        current_time = end_meet

    return {
        "itinerary": itinerary,
        "total_wait": total_wait,
        "finish_time": current_time,
        "meeting_count": len(order)
    }

def main():
    # Input variables based on the problem statement
    start_location = "Financial District"
    start_time_str = "9:00"
    start_time = time_to_minutes(start_time_str)

    travel = {
        ("Financial District", "Chinatown"): 5,
        ("Chinatown", "Financial District"): 5,
        ("Financial District", "Golden Gate Park"): 23,
        ("Chinatown", "Golden Gate Park"): 23,
        ("Golden Gate Park", "Financial District"): 26,
        ("Golden Gate Park", "Chinatown"): 23
    }

    participants = [
        {
            "name": "Kenneth",
            "location": "Chinatown",
            "avail_start": time_to_minutes("12:00"),
            "avail_end": time_to_minutes("15:00"),
            "min_duration": 90
        },
        {
            "name": "Barbara",
            "location": "Golden Gate Park",
            "avail_start": time_to_minutes("8:15"),
            "avail_end": time_to_minutes("19:00"),
            "min_duration": 45
        }
    ]

    names = [p["name"] for p in participants]
    best = None

    # Consider all non-empty subsets and their permutations to maximize number of friends met
    for r in range(len(names), 0, -1):
        feasible_found_for_r = False
        for subset in itertools.combinations(names, r):
            for order in itertools.permutations(subset):
                schedule = compute_schedule(order, start_location, start_time, participants, travel)
                if schedule is None:
                    continue
                feasible_found_for_r = True
                if best is None:
                    best = schedule
                else:
                    # Primary: maximize meeting count
                    if schedule["meeting_count"] > best["meeting_count"]:
                        best = schedule
                    elif schedule["meeting_count"] == best["meeting_count"]:
                        # Secondary: minimize total waiting time
                        if schedule["total_wait"] < best["total_wait"]:
                            best = schedule
                        elif schedule["total_wait"] == best["total_wait"]:
                            # Tertiary: minimize finish time
                            if schedule["finish_time"] < best["finish_time"]:
                                best = schedule
                            elif schedule["finish_time"] == best["finish_time"]:
                                # Quaternary: earlier first meeting start
                                if schedule["itinerary"][0]["_start_min"] < best["itinerary"][0]["_start_min"]:
                                    best = schedule
        if feasible_found_for_r:
            break  # We found the maximum r with feasible schedules

    result = {"itinerary": []}
    if best:
        # Remove internal fields and format times
        for item in best["itinerary"]:
            result["itinerary"].append({
                "action": item["action"],
                "location": item["location"],
                "person": item["person"],
                "start_time": item["start_time"],
                "end_time": item["end_time"]
            })

    print(json.dumps(result, ensure_ascii=False, indent=2))

if __name__ == "__main__":
    main()