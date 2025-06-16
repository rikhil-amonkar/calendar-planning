from z3 import *

def main():
    cities = ["Dublin", "Helsinki", "Riga", "Reykjavik", "Vienna", "Tallinn"]
    n_days = 15
    n_travel_days = n_days - 1

    dublin = 0
    helsinki = 1
    riga = 2
    reykjavik = 3
    vienna = 4
    tallinn = 5

    flights_undir = [
        (helsinki, riga),
        (riga, tallinn),
        (vienna, helsinki),
        (riga, dublin),
        (vienna, riga),
        (reykjavik, vienna),
        (helsinki, dublin),
        (tallinn, dublin),
        (reykjavik, helsinki),
        (reykjavik, dublin),
        (helsinki, tallinn),
        (vienna, dublin)
    ]

    directed_flights = []
    for (a, b) in flights_undir:
        directed_flights.append((a, b))
        directed_flights.append((b, a))

    req_days = [5, 3, 3, 2, 2, 5]

    base_city = [Int('base_city_%d' % i) for i in range(n_days)]
    travel = [Bool('travel_%d' % i) for i in range(n_travel_days)]

    s = Solver()

    for i in range(n_days):
        s.add(base_city[i] >= 0, base_city[i] <= 5)

    s.add(base_city[0] == riga)
    s.add(base_city[14] == tallinn)

    for i in range(n_travel_days):
        s.add(travel[i] == (base_city[i] != base_city[i+1]))
        allowed_flight = Or([And(base_city[i] == a, base_city[i+1] == b) for (a, b) in directed_flights])
        s.add(Implies(travel[i], allowed_flight))

    total_per_city = [0] * 6
    for c in range(6):
        total = 0
        for i in range(n_days):
            total += If(base_city[i] == c, 1, 0)
        for i in range(n_travel_days):
            total += If(And(travel[i], base_city[i+1] == c), 1, 0)
        s.add(total == req_days[c])

    s.add(Or(base_city[2] == helsinki, base_city[3] == helsinki, base_city[4] == helsinki))
    s.add(Or(base_city[1] == vienna, base_city[2] == vienna))
    s.add(Or([base_city[i] == tallinn for i in range(6, 11)]))

    s.add(Sum([If(travel[i], 1, 0) for i in range(n_travel_days)]) == 5)

    if s.check() == sat:
        m = s.model()
        base_vals = [m.evaluate(base_city[i]).as_long() for i in range(n_days)]
        travel_vals = [m.evaluate(travel[i]) for i in range(n_travel_days)]
        print("Day\tCities")
        for i in range(n_days):
            day = i + 1
            cities_today = set()
            c0 = base_vals[i]
            cities_today.add(cities[c0])
            if i < n_travel_days and is_true(travel_vals[i]):
                c1 = base_vals[i+1]
                cities_today.add(cities[c1])
            print(f"{day}\t{', '.join(sorted(cities_today))}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()