import z3
import json

def main():
    cities = ["Reykjavik", "Riga", "Oslo", "Lyon", "Dubrovnik", "Madrid", "Warsaw", "London"]
    n_days = 18
    n_cities = 8
    required_days = [4, 2, 3, 5, 2, 2, 4, 3]  # Corresponding to cities order

    bidirectional_pairs = [
        ("Warsaw", "Reykjavik"),
        ("Oslo", "Madrid"),
        ("Warsaw", "Riga"),
        ("Lyon", "London"),
        ("Madrid", "London"),
        ("Warsaw", "London"),
        ("Warsaw", "Oslo"),
        ("Oslo", "Dubrovnik"),
        ("Oslo", "Reykjavik"),
        ("Riga", "Oslo"),
        ("Oslo", "Lyon"),
        ("Oslo", "London"),
        ("London", "Reykjavik"),
        ("Warsaw", "Madrid"),
        ("Madrid", "Lyon"),
        ("Dubrovnik", "Madrid")
    ]
    unidirectional = [("Reykjavik", "Madrid")]

    allowed_flights = set()
    for a, b in bidirectional_pairs:
        idx_a = cities.index(a)
        idx_b = cities.index(b)
        allowed_flights.add((idx_a, idx_b))
        allowed_flights.add((idx_b, idx_a))
    for a, b in unidirectional:
        idx_a = cities.index(a)
        idx_b = cities.index(b)
        allowed_flights.add((idx_a, idx_b))

    s = z3.Solver()

    start_city = [z3.Int(f"start_city_{d}") for d in range(1, n_days + 1)]
    end_city = [z3.Int(f"end_city_{d}") for d in range(1, n_days + 1)]
    flight = [z3.Bool(f"flight_{d}") for d in range(1, n_days + 1)]

    for d in range(n_days):
        s.add(start_city[d] >= 0, start_city[d] < n_cities)
        s.add(end_city[d] >= 0, end_city[d] < n_cities)

    for d in range(n_days):
        s.add(flight[d] == (start_city[d] != end_city[d]))

    for d in range(1, n_days):
        s.add(start_city[d] == end_city[d - 1])

    for d in range(n_days):
        disj = []
        for (i, j) in allowed_flights:
            disj.append(z3.And(start_city[d] == i, end_city[d] == j))
        if disj:
            s.add(z3.Implies(flight[d], z3.Or(disj)))
        else:
            s.add(z3.Not(flight[d]))

    for c in range(n_cities):
        total = 0
        for d in range(n_days):
            cond = z3.Or(
                start_city[d] == c,
                z3.And(flight[d], end_city[d] == c)
            )
            total += z3.If(cond, 1, 0)
        s.add(total == required_days[c])

    day4_riga = z3.Or(
        start_city[3] == 1,
        z3.And(flight[3], end_city[3] == 1)
    )
    day5_riga = z3.Or(
        start_city[4] == 1,
        z3.And(flight[4], end_city[4] == 1)
    )
    s.add(z3.Or(day4_riga, day5_riga))

    day7_dub = z3.Or(
        start_city[6] == 4,
        z3.And(flight[6], end_city[6] == 4)
    )
    day8_dub = z3.Or(
        start_city[7] == 4,
        z3.And(flight[7], end_city[7] == 4)
    )
    s.add(z3.Or(day7_dub, day8_dub))

    if s.check() == z3.sat:
        m = s.model()
        itinerary = []
        for d in range(n_days):
            day_index = d + 1
            s_val = m.evaluate(start_city[d])
            s_city = cities[int(str(s_val))]
            itinerary.append({"day": day_index, "place": s_city})
            f_val = m.evaluate(flight[d])
            if z3.is_true(f_val):
                e_val = m.evaluate(end_city[d])
                e_city = cities[int(str(e_val))]
                itinerary.append({"day": day_index, "place": e_city})
        result = {"itinerary": itinerary}
        print(json.dumps(result))
    else:
        print('{"itinerary": []}')

if __name__ == "__main__":
    main()