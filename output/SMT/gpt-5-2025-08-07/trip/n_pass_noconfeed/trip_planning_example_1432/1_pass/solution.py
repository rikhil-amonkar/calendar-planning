import json
from z3 import *

def main():
    days = 29

    # Define cities (10 total)
    cities = [
        "Frankfurt",
        "Salzburg",
        "Athens",
        "Reykjavik",
        "Bucharest",
        "Valencia",
        "Vienna",
        "Amsterdam",
        "Stockholm",
        "Riga"
    ]
    city_index = {name: i for i, name in enumerate(cities)}
    n_cities = len(cities)

    # Build directed adjacency based on provided direct flights
    edges = set()
    def add_bi(a, b):
        edges.add((city_index[a], city_index[b]))
        edges.add((city_index[b], city_index[a]))
    def add_dir(a, b):
        edges.add((city_index[a], city_index[b]))

    # Edges (interpret "A and B" as bidirectional; "from A to B" as directed A->B)
    add_bi("Valencia", "Frankfurt")
    add_bi("Vienna", "Bucharest")
    add_dir("Valencia", "Athens")
    add_bi("Athens", "Bucharest")
    add_bi("Riga", "Frankfurt")
    add_bi("Stockholm", "Athens")
    add_bi("Amsterdam", "Bucharest")
    add_dir("Athens", "Riga")
    add_bi("Amsterdam", "Frankfurt")
    add_bi("Stockholm", "Vienna")
    add_bi("Vienna", "Riga")
    add_bi("Amsterdam", "Reykjavik")
    add_bi("Reykjavik", "Frankfurt")
    add_bi("Stockholm", "Amsterdam")
    add_bi("Amsterdam", "Valencia")
    add_bi("Vienna", "Frankfurt")
    add_bi("Valencia", "Bucharest")
    add_bi("Bucharest", "Frankfurt")
    add_bi("Stockholm", "Frankfurt")
    add_bi("Valencia", "Vienna")
    add_dir("Reykjavik", "Athens")
    add_bi("Frankfurt", "Salzburg")
    add_bi("Amsterdam", "Vienna")
    add_bi("Stockholm", "Reykjavik")
    add_bi("Amsterdam", "Riga")
    add_bi("Stockholm", "Riga")
    add_bi("Vienna", "Reykjavik")
    add_bi("Amsterdam", "Athens")
    add_bi("Athens", "Frankfurt")
    add_bi("Vienna", "Athens")
    add_bi("Riga", "Bucharest")

    # Hard planned durations (exact)
    hard_durations = {
        "Frankfurt": 4,
        "Salzburg": 5,
        "Athens": 5,
        "Reykjavik": 5,
        "Stockholm": 3,
        "Riga": 3,
        "Valencia": 2,
    }

    # Soft desired durations (optimize to equal if possible)
    soft_durations = {
        "Bucharest": 3,
        "Vienna": 5,
        "Amsterdam": 3,
    }

    # SMT variables
    opt = Optimize()

    day_city = [Int(f"city_{d}") for d in range(1, days + 1)]
    # Domain: each day assigned to one of the 10 cities
    for d in range(days):
        opt.add(Or([day_city[d] == i for i in range(n_cities)]))

    # Flight transition constraints (only direct flights when changing cities)
    for d in range(1, days):
        allowed_transitions = Or([And(day_city[d - 1] == a, day_city[d] == b) for (a, b) in edges]) if edges else False
        opt.add(Or(day_city[d] == day_city[d - 1], allowed_transitions))

    # Presence matrix: presence[c][d] indicates being in city c on day d (considering same-day flight overlap)
    presence = [[Bool(f"pres_{c}_{d}") for d in range(1, days + 1)] for c in range(n_cities)]

    for c in range(n_cities):
        # Day 1 presence
        opt.add(presence[c][0] == (day_city[0] == c))
        # Days 2..29 presence: either assigned city that day, or previous day's city if changing
        for d in range(1, days):
            opt.add(
                presence[c][d] ==
                Or(
                    day_city[d] == c,
                    And(day_city[d - 1] == c, day_city[d] != day_city[d - 1])
                )
            )

    # Count presence per city
    presence_count = {}
    for name, idx in city_index.items():
        cnt = Sum([If(presence[idx][d], 1, 0) for d in range(days)])
        presence_count[name] = cnt

    # Hard duration constraints
    for name, target in hard_durations.items():
        opt.add(presence_count[name] == target)

    # Ensure each of the 10 cities is visited at least once
    for name, idx in city_index.items():
        opt.add(Sum([If(presence[idx][d], 1, 0) for d in range(days)]) >= 1)

    # Soft duration equality constraints
    # Encourage meeting soft desired durations exactly
    for name, target in soft_durations.items():
        opt.add_soft(presence_count[name] == target, weight=10, id=f"soft_{name}")

    # Events / time-window constraints:
    # Valencia show: must be in Valencia on days 5 and 6
    val_idx = city_index["Valencia"]
    opt.add(presence[val_idx][4] == True)  # day 5
    opt.add(presence[val_idx][5] == True)  # day 6

    # Wedding in Vienna between day 6 and day 10 (at least one day)
    vie_idx = city_index["Vienna"]
    opt.add(Or([presence[vie_idx][d - 1] for d in range(6, 11)]))

    # Workshop in Athens between day 14 and day 18 (at least one day)
    ath_idx = city_index["Athens"]
    opt.add(Or([presence[ath_idx][d - 1] for d in range(14, 19)]))

    # Conference in Riga during day 18 to day 20 inclusive (must be in Riga each day)
    riga_idx = city_index["Riga"]
    opt.add(presence[riga_idx][17] == True)  # day 18
    opt.add(presence[riga_idx][18] == True)  # day 19
    opt.add(presence[riga_idx][19] == True)  # day 20

    # Meet friend in Stockholm between day 1 and day 3 (at least one day)
    sto_idx = city_index["Stockholm"]
    opt.add(Or([presence[sto_idx][d - 1] for d in range(1, 4)]))

    # Ensure Vienna, Amsterdam, Bucharest are visited at least once (hard, since we must visit 10 cities)
    for nm in ["Vienna", "Amsterdam", "Bucharest"]:
        idx = city_index[nm]
        opt.add(Sum([If(presence[idx][d], 1, 0) for d in range(days)]) >= 1)

    # Secondary objective: minimize number of city changes (to keep itinerary coherent)
    changes = [If(day_city[d] != day_city[d - 1], 1, 0) for d in range(1, days)]
    change_sum = Sum(changes)
    opt.minimize(change_sum)

    # Solve
    if opt.check() != sat:
        # In case of unexpected unsat (should not happen), relax soft durations and re-solve conservatively
        # Fallback: switch soft constraints to >= targets for soft durations
        opt2 = Optimize()
        # Rebuild (simplified) with relaxed soft eqs
        # Variables
        day_city2 = [Int(f"city2_{d}") for d in range(1, days + 1)]
        for d in range(days):
            opt2.add(Or([day_city2[d] == i for i in range(n_cities)]))
        for d in range(1, days):
            allowed_transitions2 = Or([And(day_city2[d - 1] == a, day_city2[d] == b) for (a, b) in edges]) if edges else False
            opt2.add(Or(day_city2[d] == day_city2[d - 1], allowed_transitions2))
        presence2 = [[Bool(f"pres2_{c}_{d}") for d in range(1, days + 1)] for c in range(n_cities)]
        for c in range(n_cities):
            opt2.add(presence2[c][0] == (day_city2[0] == c))
            for d in range(1, days):
                opt2.add(presence2[c][d] == Or(day_city2[d] == c, And(day_city2[d - 1] == c, day_city2[d] != day_city2[d - 1])))
        presence_count2 = {name: Sum([If(presence2[idx][d], 1, 0) for d in range(days)]) for name, idx in city_index.items()}
        for name, target in hard_durations.items():
            opt2.add(presence_count2[name] == target)
        for name in cities:
            idx = city_index[name]
            opt2.add(Sum([If(presence2[idx][d], 1, 0) for d in range(days)]) >= 1)
        # Events
        opt2.add(presence2[val_idx][4] == True)
        opt2.add(presence2[val_idx][5] == True)
        opt2.add(Or([presence2[vie_idx][d - 1] for d in range(6, 11)]))
        opt2.add(Or([presence2[ath_idx][d - 1] for d in range(14, 19)]))
        opt2.add(presence2[riga_idx][17] == True)
        opt2.add(presence2[riga_idx][18] == True)
        opt2.add(presence2[riga_idx][19] == True)
        opt2.add(Or([presence2[sto_idx][d - 1] for d in range(1, 4)]))
        # Relax soft durations to >=
        for name, target in soft_durations.items():
            opt2.add(presence_count2[name] >= target)
        changes2 = [If(day_city2[d] != day_city2[d - 1], 1, 0) for d in range(1, days)]
        opt2.minimize(Sum(changes2))
        if opt2.check() != sat:
            # As a last resort (should not occur), output empty itinerary
            print(json.dumps({"itinerary": []}))
            return
        m = opt2.model()
        final_day_city = [m[day_city2[d]].as_long() for d in range(days)]
    else:
        m = opt.model()
        final_day_city = [m[day_city[d]].as_long() for d in range(days)]

    # Build contiguous itinerary ranges by assigned city per day
    itinerary = []
    start = 1
    current_city = final_day_city[0]
    for d in range(2, days + 1):
        if final_day_city[d - 1] != current_city:
            itinerary.append({
                "day_range": f"Day {start}-{d-1}",
                "place": cities[current_city]
            })
            start = d
            current_city = final_day_city[d - 1]
    # Append last block
    itinerary.append({
        "day_range": f"Day {start}-{days}",
        "place": cities[current_city]
    })

    print(json.dumps({"itinerary": itinerary}, ensure_ascii=False))

if __name__ == "__main__":
    main()