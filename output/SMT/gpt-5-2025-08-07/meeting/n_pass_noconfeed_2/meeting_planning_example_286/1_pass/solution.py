import json
from itertools import combinations, permutations
from z3 import Int, Optimize, Sum, sat

def minutes(h, m):
    return h * 60 + m

def fmt_time(t):
    h = t // 60
    m = t % 60
    return f"{h}:{m:02d}"

def build_travel():
    # Directed travel times in minutes
    return {
        ("Union Square", "Mission District"): 14,
        ("Union Square", "Bayview"): 15,
        ("Union Square", "Sunset District"): 26,
        ("Mission District", "Union Square"): 15,
        ("Mission District", "Bayview"): 15,
        ("Mission District", "Sunset District"): 24,
        ("Bayview", "Union Square"): 17,
        ("Bayview", "Mission District"): 13,
        ("Bayview", "Sunset District"): 23,
        ("Sunset District", "Union Square"): 30,
        ("Sunset District", "Mission District"): 24,
        ("Sunset District", "Bayview"): 22,
    }

def main():
    start_location = "Union Square"
    arrival_time = minutes(9, 0)

    travel = build_travel()

    people = [
        {
            "name": "Rebecca",
            "location": "Mission District",
            "avail_start": minutes(11, 30),
            "avail_end": minutes(20, 15),
            "min_duration": 120
        },
        {
            "name": "Karen",
            "location": "Bayview",
            "avail_start": minutes(12, 45),
            "avail_end": minutes(15, 0),
            "min_duration": 120
        },
        {
            "name": "Carol",
            "location": "Sunset District",
            "avail_start": minutes(10, 15),
            "avail_end": minutes(11, 45),
            "min_duration": 30
        }
    ]

    def solve_for_order(order_indices):
        s = Optimize()
        n = len(order_indices)
        starts = []
        ends = []
        # Create variables and constraints per person in this order
        for idx_pos, p_idx in enumerate(order_indices):
            p = people[p_idx]
            st = Int(f"start_{p['name']}")
            en = Int(f"end_{p['name']}")
            starts.append(st)
            ends.append(en)
            # Availability window and minimum duration
            s.add(st >= p["avail_start"])
            s.add(en <= p["avail_end"])
            s.add(en - st >= p["min_duration"])
        # Travel constraints from initial location
        if n > 0:
            first = people[order_indices[0]]
            s.add(starts[0] >= arrival_time + travel[(start_location, first["location"])])
            # Sequential travel constraints between meetings
            for k in range(1, n):
                prev = people[order_indices[k-1]]
                cur = people[order_indices[k]]
                s.add(starts[k] >= ends[k-1] + travel[(prev["location"], cur["location"])])
        # Objective: maximize total meeting time
        total_meeting_time = Sum([ends[i] - starts[i] for i in range(n)]) if n > 0 else Int("zero")
        if n > 0:
            s.maximize(total_meeting_time)
        if s.check() != sat:
            return None
        m = s.model()
        itinerary = []
        total_time_val = 0
        for k, p_idx in enumerate(order_indices):
            p = people[p_idx]
            st_val = m.eval(starts[k]).as_long()
            en_val = m.eval(ends[k]).as_long()
            total_time_val += en_val - st_val
            itinerary.append({
                "action": "meet",
                "location": p["location"],
                "person": p["name"],
                "start_time": fmt_time(st_val),
                "end_time": fmt_time(en_val)
            })
        return {"itinerary": itinerary, "total_meeting_time": total_time_val, "count": len(itinerary)}

    best_plan = None

    indices = list(range(len(people)))
    # Try to maximize number of meetings first
    for size in range(len(people), 0, -1):
        candidate_plans = []
        for subset in combinations(indices, size):
            for order in permutations(subset):
                result = solve_for_order(order)
                if result is not None:
                    candidate_plans.append(result)
        if candidate_plans:
            # Choose the plan with maximum total meeting time as tie-breaker
            best_plan = max(candidate_plans, key=lambda r: (r["count"], r["total_meeting_time"]))
            break

    output = {"itinerary": []}
    if best_plan:
        output["itinerary"] = best_plan["itinerary"]

    print(json.dumps(output))

if __name__ == "__main__":
    main()