# SOLUTION:
import itertools
import json

def to_minutes(s):
    s = s.strip().upper()
    if s.endswith("AM") or s.endswith("PM"):
        ampm = s[-2:]
        hh, mm = s[:-2].split(":")
        h = int(hh)
        m = int(mm)
        if ampm == "AM":
            if h == 12:
                h = 0
        else:
            if h != 12:
                h += 12
        return h * 60 + m
    else:
        hh, mm = s.split(":")
        return int(hh) * 60 + int(mm)

def to_hm(m):
    h = m // 60
    mm = m % 60
    return f"{h}:{mm:02d}"

def build_travel_times():
    return {
        "Golden Gate Park": {
            "Haight-Ashbury": 7,
            "Sunset District": 10,
            "Marina District": 16,
            "Financial District": 26,
            "Union Square": 22
        },
        "Haight-Ashbury": {
            "Golden Gate Park": 7,
            "Sunset District": 15,
            "Marina District": 17,
            "Financial District": 21,
            "Union Square": 17
        },
        "Sunset District": {
            "Golden Gate Park": 11,
            "Haight-Ashbury": 15,
            "Marina District": 21,
            "Financial District": 30,
            "Union Square": 30
        },
        "Marina District": {
            "Golden Gate Park": 18,
            "Haight-Ashbury": 16,
            "Sunset District": 19,
            "Financial District": 17,
            "Union Square": 16
        },
        "Financial District": {
            "Golden Gate Park": 23,
            "Haight-Ashbury": 19,
            "Sunset District": 31,
            "Marina District": 15,
            "Union Square": 9
        },
        "Union Square": {
            "Golden Gate Park": 22,
            "Haight-Ashbury": 18,
            "Sunset District": 26,
            "Marina District": 18,
            "Financial District": 9
        }
    }

def compute_optimal_itinerary(start_location, start_time, people, travel):
    best = {
        "count": -1,
        "wait": float("inf"),
        "end_time": float("inf"),
        "travel": float("inf"),
        "itinerary": []
    }

    persons = people[:]
    for order in itertools.permutations(persons, len(persons)):
        time = start_time
        loc = start_location
        itinerary = []
        total_wait = 0
        total_travel = 0

        for person in order:
            from_loc = loc
            to_loc = person["location"]
            # Travel time must exist
            if from_loc not in travel or to_loc not in travel[from_loc]:
                continue  # skip if travel time unknown
            t_travel = travel[from_loc][to_loc]
            arrival = time + t_travel
            start_meet = max(arrival, person["start"])
            end_meet = start_meet + person["min_duration"]
            if end_meet <= person["end"]:
                # feasible meeting
                total_wait += max(0, start_meet - arrival)
                total_travel += t_travel
                itinerary.append({
                    "action": "meet",
                    "location": to_loc,
                    "person": person["name"],
                    "start_time": to_hm(start_meet),
                    "end_time": to_hm(end_meet)
                })
                time = end_meet
                loc = to_loc
            else:
                # cannot meet this person in this sequence step; skip
                continue

        count = len(itinerary)
        # Tie-breakers: maximize count, then minimize total wait, then earliest end time, then minimize travel
        better = False
        if count > best["count"]:
            better = True
        elif count == best["count"]:
            if total_wait < best["wait"]:
                better = True
            elif total_wait == best["wait"]:
                if time < best["end_time"]:
                    better = True
                elif time == best["end_time"]:
                    if total_travel < best["travel"]:
                        better = True

        if better:
            best = {
                "count": count,
                "wait": total_wait,
                "end_time": time,
                "travel": total_travel,
                "itinerary": itinerary
            }

    return best["itinerary"]

def main():
    # Input variables
    start_location = "Golden Gate Park"
    start_time = to_minutes("9:00AM")

    people = [
        {
            "name": "Sarah",
            "location": "Haight-Ashbury",
            "start": to_minutes("5:00PM"),
            "end": to_minutes("9:30PM"),
            "min_duration": 105
        },
        {
            "name": "Patricia",
            "location": "Sunset District",
            "start": to_minutes("5:00PM"),
            "end": to_minutes("7:45PM"),
            "min_duration": 45
        },
        {
            "name": "Matthew",
            "location": "Marina District",
            "start": to_minutes("9:15AM"),
            "end": to_minutes("12:00PM"),
            "min_duration": 15
        },
        {
            "name": "Joseph",
            "location": "Financial District",
            "start": to_minutes("2:15PM"),
            "end": to_minutes("6:45PM"),
            "min_duration": 30
        },
        {
            "name": "Robert",
            "location": "Union Square",
            "start": to_minutes("10:15AM"),
            "end": to_minutes("9:45PM"),
            "min_duration": 15
        }
    ]

    travel = build_travel_times()

    itinerary = compute_optimal_itinerary(start_location, start_time, people, travel)

    output = {
        "itinerary": itinerary
    }
    print(json.dumps(output, ensure_ascii=False))

if __name__ == "__main__":
    main()