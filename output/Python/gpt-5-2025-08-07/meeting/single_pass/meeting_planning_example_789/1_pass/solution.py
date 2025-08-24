import json
from copy import deepcopy

def time_to_minutes(tstr):
    # tstr format examples: '9:00', '13:30'
    h, m = map(int, tstr.split(':'))
    return h * 60 + m

def minutes_to_time(m):
    h = m // 60
    mi = m % 60
    return f"{h}:{mi:02d}"

def build_travel_times():
    locs = [
        "Union Square", "Russian Hill", "Alamo Square", "Haight-Ashbury",
        "Marina District", "Bayview", "Chinatown", "Presidio", "Sunset District"
    ]
    T = {a: {} for a in locs}
    # Union Square
    T["Union Square"]["Russian Hill"] = 13
    T["Union Square"]["Alamo Square"] = 15
    T["Union Square"]["Haight-Ashbury"] = 18
    T["Union Square"]["Marina District"] = 18
    T["Union Square"]["Bayview"] = 15
    T["Union Square"]["Chinatown"] = 7
    T["Union Square"]["Presidio"] = 24
    T["Union Square"]["Sunset District"] = 27
    # Russian Hill
    T["Russian Hill"]["Union Square"] = 10
    T["Russian Hill"]["Alamo Square"] = 15
    T["Russian Hill"]["Haight-Ashbury"] = 17
    T["Russian Hill"]["Marina District"] = 7
    T["Russian Hill"]["Bayview"] = 23
    T["Russian Hill"]["Chinatown"] = 9
    T["Russian Hill"]["Presidio"] = 14
    T["Russian Hill"]["Sunset District"] = 23
    # Alamo Square
    T["Alamo Square"]["Union Square"] = 14
    T["Alamo Square"]["Russian Hill"] = 13
    T["Alamo Square"]["Haight-Ashbury"] = 5
    T["Alamo Square"]["Marina District"] = 15
    T["Alamo Square"]["Bayview"] = 16
    T["Alamo Square"]["Chinatown"] = 15
    T["Alamo Square"]["Presidio"] = 17
    T["Alamo Square"]["Sunset District"] = 16
    # Haight-Ashbury
    T["Haight-Ashbury"]["Union Square"] = 19
    T["Haight-Ashbury"]["Russian Hill"] = 17
    T["Haight-Ashbury"]["Alamo Square"] = 5
    T["Haight-Ashbury"]["Marina District"] = 17
    T["Haight-Ashbury"]["Bayview"] = 18
    T["Haight-Ashbury"]["Chinatown"] = 19
    T["Haight-Ashbury"]["Presidio"] = 15
    T["Haight-Ashbury"]["Sunset District"] = 15
    # Marina District
    T["Marina District"]["Union Square"] = 16
    T["Marina District"]["Russian Hill"] = 8
    T["Marina District"]["Alamo Square"] = 15
    T["Marina District"]["Haight-Ashbury"] = 16
    T["Marina District"]["Bayview"] = 27
    T["Marina District"]["Chinatown"] = 15
    T["Marina District"]["Presidio"] = 10
    T["Marina District"]["Sunset District"] = 19
    # Bayview
    T["Bayview"]["Union Square"] = 18
    T["Bayview"]["Russian Hill"] = 23
    T["Bayview"]["Alamo Square"] = 16
    T["Bayview"]["Haight-Ashbury"] = 19
    T["Bayview"]["Marina District"] = 27
    T["Bayview"]["Chinatown"] = 19
    T["Bayview"]["Presidio"] = 32
    T["Bayview"]["Sunset District"] = 23
    # Chinatown
    T["Chinatown"]["Union Square"] = 7
    T["Chinatown"]["Russian Hill"] = 7
    T["Chinatown"]["Alamo Square"] = 17
    T["Chinatown"]["Haight-Ashbury"] = 19
    T["Chinatown"]["Marina District"] = 12
    T["Chinatown"]["Bayview"] = 20
    T["Chinatown"]["Presidio"] = 19
    T["Chinatown"]["Sunset District"] = 29
    # Presidio
    T["Presidio"]["Union Square"] = 22
    T["Presidio"]["Russian Hill"] = 14
    T["Presidio"]["Alamo Square"] = 19
    T["Presidio"]["Haight-Ashbury"] = 15
    T["Presidio"]["Marina District"] = 11
    T["Presidio"]["Bayview"] = 31
    T["Presidio"]["Chinatown"] = 21
    T["Presidio"]["Sunset District"] = 15
    # Sunset District
    T["Sunset District"]["Union Square"] = 30
    T["Sunset District"]["Russian Hill"] = 24
    T["Sunset District"]["Alamo Square"] = 17
    T["Sunset District"]["Haight-Ashbury"] = 15
    T["Sunset District"]["Marina District"] = 21
    T["Sunset District"]["Bayview"] = 22
    T["Sunset District"]["Chinatown"] = 30
    T["Sunset District"]["Presidio"] = 16

    # Fill self travel as 0
    for a in locs:
        T[a][a] = 0
    return T

def build_people():
    # Windows in minutes from midnight
    def hm(h, m):
        return h * 60 + m
    people = {
        "Betty": {
            "location": "Russian Hill",
            "start": hm(7, 0),
            "end": hm(16, 45),
            "min_duration": 105
        },
        "Melissa": {
            "location": "Alamo Square",
            "start": hm(9, 30),
            "end": hm(17, 15),
            "min_duration": 105
        },
        "Joshua": {
            "location": "Haight-Ashbury",
            "start": hm(12, 15),
            "end": hm(19, 0),
            "min_duration": 90
        },
        "Jeffrey": {
            "location": "Marina District",
            "start": hm(12, 15),
            "end": hm(18, 0),
            "min_duration": 45
        },
        "James": {
            "location": "Bayview",
            "start": hm(7, 30),
            "end": hm(20, 0),
            "min_duration": 90
        },
        "Anthony": {
            "location": "Chinatown",
            "start": hm(11, 45),
            "end": hm(13, 30),
            "min_duration": 75
        },
        "Timothy": {
            "location": "Presidio",
            "start": hm(12, 30),
            "end": hm(14, 45),
            "min_duration": 90
        },
        "Emily": {
            "location": "Sunset District",
            "start": hm(19, 30),
            "end": hm(21, 30),
            "min_duration": 120
        }
    }
    return people

def compute_optimal_schedule():
    travel = build_travel_times()
    people = build_people()
    start_location = "Union Square"
    start_time = time_to_minutes("9:00")

    names = list(people.keys())

    best = {
        "count": -1,
        "finish_time": float('inf'),
        "itinerary": []
    }

    # DFS search over all feasible sequences (choose earliest feasible start for each meeting)
    def dfs(current_location, current_time, remaining_names, itinerary):
        nonlocal best

        met_count = len(itinerary)
        finish_time = current_time

        # Update best if better
        if met_count > best["count"] or (met_count == best["count"] and finish_time < best["finish_time"]):
            best = {
                "count": met_count,
                "finish_time": finish_time,
                "itinerary": deepcopy(itinerary)
            }

        # Try to meet each remaining person next
        for name in remaining_names:
            person = people[name]
            t_travel = travel[current_location][person["location"]]
            arrival = current_time + t_travel
            start = max(arrival, person["start"])
            end = start + person["min_duration"]
            if end <= person["end"]:
                new_itinerary = itinerary + [{
                    "action": "meet",
                    "location": person["location"],
                    "person": name,
                    "start_time": minutes_to_time(start),
                    "end_time": minutes_to_time(end)
                }]
                new_remaining = [n for n in remaining_names if n != name]
                dfs(person["location"], end, new_remaining, new_itinerary)

    dfs(start_location, start_time, names, [])

    # Prepare output as required JSON
    return {"itinerary": best["itinerary"]}

if __name__ == "__main__":
    result = compute_optimal_schedule()
    print(json.dumps(result, ensure_ascii=False))