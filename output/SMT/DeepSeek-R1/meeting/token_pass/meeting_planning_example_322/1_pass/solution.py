import json
from z3 import *

def main():
    # Travel times matrix
    travel_times = {
        "Sunset District": {
            "Russian Hill": 24,
            "Chinatown": 30,
            "Presidio": 16,
            "Fisherman's Wharf": 29
        },
        "Russian Hill": {
            "Sunset District": 23,
            "Chinatown": 9,
            "Presidio": 14,
            "Fisherman's Wharf": 7
        },
        "Chinatown": {
            "Sunset District": 29,
            "Russian Hill": 7,
            "Presidio": 19,
            "Fisherman's Wharf": 8
        },
        "Presidio": {
            "Sunset District": 15,
            "Russian Hill": 14,
            "Chinatown": 21,
            "Fisherman's Wharf": 19
        },
        "Fisherman's Wharf": {
            "Sunset District": 27,
            "Russian Hill": 7,
            "Chinatown": 12,
            "Presidio": 17
        }
    }

    # Friends data: name, location, available start/end (minutes from 9:00 AM), min meeting time
    friends = [
        {"name": "William", "location": "Russian Hill", "start_avail": 570, "end_avail": 705, "min_time": 105},
        {"name": "Michelle", "location": "Chinatown", "start_avail": -45, "end_avail": 300, "min_time": 15},
        {"name": "George", "location": "Presidio", "start_avail": 90, "end_avail": 585, "min_time": 30},
        {"name": "Robert", "location": "Fisherman's Wharf", "start_avail": 0, "end_avail": 285, "min_time": 30}
    ]

    # Initialize solver
    opt = Optimize()
    n = len(friends)

    # Create variables for each friend
    s = [Int(f"s_{i}") for i in range(n)]
    e = [Int(f"e_{i}") for i in range(n)]
    met = [Bool(f"met_{i}") for i in range(n)]
    order = [Int(f"order_{i}") for i in range(n)]

    # Constraints for each meeting
    for i, f in enumerate(friends):
        # Time window and duration constraints if meeting occurs
        opt.add(Implies(met[i], And(
            s[i] >= max(0, f["start_avail"]),
            e[i] <= f["end_avail"],
            e[i] - s[i] >= f["min_time"],
            order[i] >= 0,
            order[i] < n
        )))
        # Default values if meeting doesn't occur
        opt.add(Implies(Not(met[i]), And(s[i] == 0, e[i] == 0, order[i] == -1)))

    # Ordering and travel time constraints
    for i in range(n):
        for j in range(n):
            if i != j:
                opt.add(Implies(
                    And(met[i], met[j], order[i] < order[j]),
                    e[i] + travel_times[friends[i]["location"]][friends[j]["location"]] <= s[j]
                ))

    # Initial travel from Sunset District
    for i in range(n):
        opt.add(Implies(
            And(met[i], order[i] == 0),
            s[i] >= travel_times["Sunset District"][friends[i]["location"]]
        ))

    # Distinct order for scheduled meetings
    opt.add(Distinct([If(met[i], order[i], -1) for i in range(n)]))

    # Maximize number of meetings
    opt.maximize(Sum([If(met[i], 1, 0) for i in range(n)]))

    # Convert minutes to time string (e.g., 90 -> "10:30")
    def min_to_time(m):
        total_min = 540 + m  # 9:00 AM base
        h = total_min // 60
        m = total_min % 60
        return f"{h}:{m:02d}"

    # Solve and output
    if opt.check() == sat:
        model = opt.model()
        itinerary = []
        for i, f in enumerate(friends):
            if model.eval(met[i]):
                start_val = model.eval(s[i])
                end_val = model.eval(e[i])
                start_min = start_val.as_long()
                end_min = end_val.as_long()
                itinerary.append({
                    "action": "meet",
                    "location": f["location"],
                    "person": f["name"],
                    "start_time": min_to_time(start_min),
                    "end_time": min_to_time(end_min)
                })
        itinerary.sort(key=lambda x: x["start_time"])
        print(json.dumps({"itinerary": itinerary}, indent=2))
    else:
        print('{"itinerary": []}')

if __name__ == "__main__":
    main()