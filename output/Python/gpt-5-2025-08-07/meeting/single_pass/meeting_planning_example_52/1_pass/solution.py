# SOLUTION:
import json
from itertools import permutations

def time_to_minutes(tstr):
    # tstr format like '9:00' or '13:30'
    parts = tstr.split(":")
    hour = int(parts[0])
    minute = int(parts[1])
    return hour * 60 + minute

def minutes_to_time(m):
    h = m // 60
    mm = m % 60
    return f"{h}:{mm:02d}"

def attempt_schedule(order, start_loc, start_time_min, travel):
    current_loc = start_loc
    current_time = start_time_min
    itinerary = []

    for friend in order:
        loc = friend["location"]
        # Determine travel time; if same location, no travel time
        if current_loc == loc:
            t_travel = 0
        else:
            t_travel = travel.get((current_loc, loc), None)
            if t_travel is None:
                # No route known; fail this friend
                continue

        earliest_arrival = current_time + t_travel

        avail_start = time_to_minutes(friend["avail_start"])
        avail_end = time_to_minutes(friend["avail_end"])
        min_dur = friend["min_duration"]

        # Meeting can start at max(availability start, arrival time)
        start_meet = max(earliest_arrival, avail_start)
        end_meet = start_meet + min_dur

        if end_meet <= avail_end:
            itinerary.append({
                "action": "meet",
                "location": loc,
                "person": friend["name"],
                "start_time": minutes_to_time(start_meet),
                "end_time": minutes_to_time(end_meet),
                "_start_min": start_meet,
                "_end_min": end_meet
            })
            current_loc = loc
            current_time = end_meet
        # else can't meet due to insufficient window

    return itinerary

def optimize_schedule(friends, start_loc, start_time_str, travel):
    start_time_min = time_to_minutes(start_time_str)

    best_itinerary = []
    best_finish_time = None

    # Consider different orders of meeting friends (various schedules)
    for order in permutations(friends, len(friends)):
        itinerary = attempt_schedule(order, start_loc, start_time_min, travel)

        # Objective 1: maximize number of meetings
        if len(itinerary) > len(best_itinerary):
            best_itinerary = itinerary
            best_finish_time = itinerary[-1]["_end_min"] if itinerary else start_time_min
        elif len(itinerary) == len(best_itinerary):
            # Tie-breaker: earliest finish time
            finish_time = itinerary[-1]["_end_min"] if itinerary else start_time_min
            if best_finish_time is None or (finish_time is not None and finish_time < best_finish_time):
                best_itinerary = itinerary
                best_finish_time = finish_time

    # Strip internal fields before output
    for item in best_itinerary:
        item.pop("_start_min", None)
        item.pop("_end_min", None)

    return best_itinerary

def main():
    # Input parameters
    start_location = "Russian Hill"
    arrival_time_at_start_location = "9:00"

    travel_times = {
        ("Russian Hill", "Richmond District"): 14,
        ("Richmond District", "Russian Hill"): 13
    }

    friends = [
        {
            "name": "Barbara",
            "location": "Richmond District",
            "avail_start": "13:15",
            "avail_end": "18:15",
            "min_duration": 45
        }
    ]

    itinerary = optimize_schedule(friends, start_location, arrival_time_at_start_location, travel_times)

    output = {
        "itinerary": itinerary
    }

    print(json.dumps(output, ensure_ascii=False))

if __name__ == "__main__":
    main()