import itertools
import json

def to_minutes(h, m):
    return h * 60 + m

def fmt_time(total_minutes):
    h = total_minutes // 60
    m = total_minutes % 60
    return f"{h}:{m:02d}"

def plan_schedule(start_loc, start_time, people, travel):
    # Explore all subsets and permutations to maximize number of friends met
    best = None  # (count, end_time, total_wait, total_travel, itinerary)
    n = len(people)
    # Generate all subsets (size n down to 1) and permutations
    for r in range(n, 0, -1):
        for combo in itertools.combinations(people, r):
            for order in itertools.permutations(combo):
                current_loc = start_loc
                current_time = start_time
                itinerary = []
                feasible = True
                total_wait = 0
                total_travel = 0
                for p in order:
                    t_travel = 0 if current_loc == p['location'] else travel[current_loc][p['location']]
                    total_travel += t_travel
                    arrival = current_time + t_travel
                    start_meet = max(arrival, p['start'])
                    end_meet = start_meet + p['min_dur']
                    if end_meet > p['end']:
                        feasible = False
                        break
                    wait = max(0, start_meet - arrival)
                    total_wait += wait
                    itinerary.append({
                        "action": "meet",
                        "location": p['location'],
                        "person": p['name'],
                        "start_time": fmt_time(start_meet),
                        "end_time": fmt_time(end_meet)
                    })
                    current_loc = p['location']
                    current_time = end_meet
                if feasible:
                    count = len(itinerary)
                    end_time = current_time
                    score = (count, -end_time, -total_wait, -total_travel)  # maximize count, then earlier end, less wait, less travel
                    if best is None or score > best[0]:
                        best = (score, itinerary)
        if best is not None and best[0][0] == r:
            # Found best possible for this r (max count); no need to check smaller subsets
            break
    return best[1] if best else []

def main():
    # Input variables (constraints and travel times)
    start_location = "Fisherman's Wharf"
    start_time = to_minutes(9, 0)

    # Travel times (directed, in minutes)
    travel = {
        "Fisherman's Wharf": {
            "Presidio": 17,
            "Richmond District": 18,
            "Financial District": 11
        },
        "Presidio": {
            "Fisherman's Wharf": 19,
            "Richmond District": 7,
            "Financial District": 23
        },
        "Richmond District": {
            "Fisherman's Wharf": 18,
            "Presidio": 7,
            "Financial District": 22
        },
        "Financial District": {
            "Fisherman's Wharf": 10,
            "Presidio": 22,
            "Richmond District": 21
        }
    }

    people = [
        {
            "name": "Emily",
            "location": "Presidio",
            "start": to_minutes(16, 15),
            "end": to_minutes(21, 0),
            "min_dur": 105
        },
        {
            "name": "Joseph",
            "location": "Richmond District",
            "start": to_minutes(17, 15),
            "end": to_minutes(22, 0),
            "min_dur": 120
        },
        {
            "name": "Melissa",
            "location": "Financial District",
            "start": to_minutes(15, 45),
            "end": to_minutes(21, 45),
            "min_dur": 75
        }
    ]

    itinerary = plan_schedule(start_location, start_time, people, travel)
    output = {"itinerary": itinerary}
    print(json.dumps(output, ensure_ascii=False))

if __name__ == "__main__":
    main()