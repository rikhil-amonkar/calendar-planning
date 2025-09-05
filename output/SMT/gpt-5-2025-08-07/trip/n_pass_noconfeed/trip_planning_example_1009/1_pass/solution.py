import json
from z3 import *

def main():
    # Define cities and indices
    cities = ["Riga","Manchester","Bucharest","Florence","Vienna","Istanbul","Reykjavik","Stuttgart"]
    idx = {name:i for i,name in enumerate(cities)}

    # Desired durations (days counted per problem's rule: flight day counts for both cities)
    desired = {
        "Riga": 4,
        "Manchester": 5,
        "Bucharest": 4,
        "Florence": 4,
        "Vienna": 2,
        "Istanbul": 2,
        "Reykjavik": 4,
        "Stuttgart": 5
    }

    total_days = 23

    # Allowed direct flights (directed where specified)
    allowed_pairs = set()
    def add_bidirectional(a,b):
        allowed_pairs.add((idx[a], idx[b]))
        allowed_pairs.add((idx[b], idx[a]))
    def add_direct(a,b):
        allowed_pairs.add((idx[a], idx[b]))

    add_bidirectional("Bucharest","Vienna")
    add_bidirectional("Reykjavik","Vienna")
    add_bidirectional("Manchester","Vienna")
    add_bidirectional("Manchester","Riga")
    add_bidirectional("Riga","Vienna")
    add_bidirectional("Istanbul","Vienna")
    add_bidirectional("Vienna","Florence")
    add_bidirectional("Stuttgart","Vienna")
    add_bidirectional("Riga","Bucharest")
    add_bidirectional("Istanbul","Riga")
    add_bidirectional("Stuttgart","Istanbul")
    add_direct("Reykjavik","Stuttgart")  # directed only
    add_bidirectional("Istanbul","Bucharest")
    add_bidirectional("Manchester","Istanbul")
    add_bidirectional("Manchester","Bucharest")
    add_bidirectional("Stuttgart","Manchester")

    # Helper to build allowed transition expression for two Int vars x,y
    def allowed_transition_expr(x, y):
        return Or(*[And(x == a, y == b) for (a,b) in allowed_pairs])

    # Z3 variables: city per day (0-based days 0..22 correspond to Day 1..23)
    days = list(range(total_days))
    city = [Int(f"city_{d}") for d in days]

    s = Solver()

    # Domain constraints
    for d in days:
        s.add(And(city[d] >= 0, city[d] < len(cities)))

    # Transition constraints: if a change occurs, it must be an allowed direct flight
    for d in range(total_days - 1):
        s.add(Or(city[d] == city[d+1], allowed_transition_expr(city[d], city[d+1])))

    # Presence indicator per day and city, derived from rule:
    # On day d, you are present in city C if:
    #   city[d] == C (assigned), OR
    #   d < last_day and city[d] != city[d+1] and city[d+1] == C (arrival on day d)
    def present_expr(day_index, city_index):
        if day_index < total_days - 1:
            return Or(
                city[day_index] == city_index,
                And(city[day_index] != city[day_index+1], city[day_index+1] == city_index)
            )
        else:
            # On the last day, presence only if assigned that day (no arrival from a next day)
            return city[day_index] == city_index

    # Duration constraints exactly match desired days
    for name, req in desired.items():
        c = idx[name]
        presence_count = Sum([If(present_expr(d, c), 1, 0) for d in days])
        s.add(presence_count == req)

    # The sum of transitions equals sum(desired) - total_days
    # transitions = number of days where city[d] != city[d+1]
    transitions = Sum([If(city[d] != city[d+1], 1, 0) for d in range(total_days - 1)])
    s.add(transitions == sum(desired.values()) - total_days)

    # Event constraints:
    # Istanbul presence on Day 12 and Day 13 (indices 11 and 12)
    s.add(present_expr(11, idx["Istanbul"]))
    s.add(present_expr(12, idx["Istanbul"]))

    # Bucharest presence on Days 16-19 (indices 15..18)
    for d in range(15, 19):
        s.add(present_expr(d, idx["Bucharest"]))

    # Solve
    if s.check() != sat:
        print(json.dumps({"itinerary": [], "status": "unsat"}))
        return

    m = s.model()
    city_by_day = [m.evaluate(city[d]).as_long() for d in days]

    # Build itinerary as compressed day ranges of assigned city
    itinerary = []
    start = 0
    for d in range(1, total_days):
        if city_by_day[d] != city_by_day[d-1]:
            # close previous segment
            itinerary.append({
                "day_range": f"Day {start+1}-{d}",
                "place": cities[city_by_day[start]]
            })
            start = d
    # close last segment
    itinerary.append({
        "day_range": f"Day {start+1}-{total_days}",
        "place": cities[city_by_day[start]]
    })

    print(json.dumps({"itinerary": itinerary}, ensure_ascii=False))

if __name__ == "__main__":
    main()