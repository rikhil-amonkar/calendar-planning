from z3 import *
import json

def main():
    cities = ["Brussels", "Helsinki", "Split", "Dubrovnik", "Istanbul", "Milan", "Vilnius", "Frankfurt"]
    n_cities = len(cities)
    n_days = 22

    flight_strings = [
        "Milan and Frankfurt",
        "Split and Frankfurt",
        "Milan and Split",
        "Brussels and Vilnius",
        "Brussels and Helsinki",
        "Istanbul and Brussels",
        "Milan and Vilnius",
        "Brussels and Milan",
        "Istanbul and Helsinki",
        "Helsinki and Vilnius",
        "Helsinki and Dubrovnik",
        "Split and Vilnius",
        "from Dubrovnik to Istanbul",
        "Istanbul and Milan",
        "Helsinki and Frankfurt",
        "Istanbul and Vilnius",
        "Split and Helsinki",
        "Milan and Helsinki",
        "Istanbul and Frankfurt",
        "from Brussels to Frankfurt",
        "Dubrovnik and Frankfurt",
        "Frankfurt and Vilnius"
    ]

    edges_set = set()
    for s in flight_strings:
        if s.startswith("from"):
            parts = s.split()
            city1 = parts[1]
            city2 = parts[3]
        else:
            parts = s.split()
            if len(parts) == 3 and parts[1] == 'and':
                city1, city2 = parts[0], parts[2]
            else:
                parts2 = s.split(" and ")
                if len(parts2) == 2:
                    city1, city2 = parts2
                else:
                    continue
        try:
            idx1 = cities.index(city1)
            idx2 = cities.index(city2)
        except:
            continue
        u = min(idx1, idx2)
        v = max(idx1, idx2)
        edges_set.add((u, v))
    
    edges_list = list(edges_set)

    s = Solver()

    in_city = [ [ Bool(f"in_{i}_{d}") for d in range(1, n_days+1) ] for i in range(n_cities) ]
    flight = [ Bool(f"flight_{d}") for d in range(1, n_days+1) ]
    end_city = [ Int(f"end_city_{d}") for d in range(1, n_days+1) ]

    for d in range(n_days):
        s.add(end_city[d] >= 0, end_city[d] < n_cities)

    for d in range(1, n_days+1):
        d_idx = d-1
        if d == 1:
            start = 4
        else:
            start = end_city[d_idx-1]

        flight_d = flight[d_idx]
        end_d = end_city[d_idx]

        if d == n_days:
            s.add(end_d == 6)

        condition = Or([ Or(And(start == u, end_d == v), And(start == v, end_d == u)) for (u, v) in edges_list ])
        s.add(Implies(flight_d, And(start != end_d, condition)))
        s.add(Implies(Not(flight_d), start == end_d))

        for i in range(n_cities):
            if i == start:
                s.add(Implies(Not(flight_d), in_city[i][d_idx] == True))
                s.add(Implies(flight_d, in_city[i][d_idx] == True))
            elif i == end_d:
                s.add(Implies(flight_d, in_city[i][d_idx] == True))
                s.add(Implies(Not(flight_d), in_city[i][d_idx] == False))
            else:
                s.add(in_city[i][d_idx] == False)

    for d in range(1, 6):
        s.add(in_city[4][d-1] == True)

    for d in range(16, 19):
        s.add(in_city[7][d-1] == True)

    for d in range(18, 23):
        s.add(in_city[6][d-1] == True)

    total_days = [0] * n_cities
    for i in range(n_cities):
        total_days[i] = Sum([If(in_city[i][d], 1, 0) for d in range(n_days)])
    s.add(total_days[0] == 3)
    s.add(total_days[1] == 3)
    s.add(total_days[2] == 4)
    s.add(total_days[3] == 2)
    s.add(total_days[4] == 5)
    s.add(total_days[5] == 4)
    s.add(total_days[6] == 5)
    s.add(total_days[7] == 3)

    if s.check() == sat:
        m = s.model()
        itinerary = []
        for d in range(1, n_days+1):
            d_idx = d-1
            for i in range(n_cities):
                if m.evaluate(in_city[i][d_idx]):
                    itinerary.append({"day": d, "place": cities[i]})
        result = {"itinerary": itinerary}
        print(json.dumps(result))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()