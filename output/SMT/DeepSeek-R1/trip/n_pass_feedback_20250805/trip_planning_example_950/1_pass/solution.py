from z3 import *

def main():
    cities = ["Rome", "Mykonos", "Nice", "Riga", "Bucharest", "Munich", "Krakow"]
    required_days = {
        "Rome": 4,
        "Mykonos": 3,
        "Nice": 3,
        "Riga": 3,
        "Bucharest": 4,
        "Munich": 4,
        "Krakow": 2
    }

    bidirectional_flights = [
        ("Nice", "Riga"),
        ("Bucharest", "Munich"),
        ("Mykonos", "Munich"),
        ("Riga", "Bucharest"),
        ("Rome", "Nice"),
        ("Rome", "Munich"),
        ("Mykonos", "Nice"),
        ("Rome", "Mykonos"),
        ("Munich", "Krakow"),
        ("Rome", "Bucharest"),
        ("Nice", "Munich")
    ]

    directed_flights = [
        ("Riga", "Munich"),
        ("Rome", "Riga")
    ]

    allowed_edges = set()
    for a, b in bidirectional_flights:
        allowed_edges.add((a, b))
        allowed_edges.add((b, a))
    for a, b in directed_flights:
        allowed_edges.add((a, b))

    s = Solver()

    first_city = "Rome"
    last_city = "Krakow"
    other_cities = [c for c in cities if c != first_city and c != last_city]

    CitySort = Datatype('CitySort')
    for c in cities:
        CitySort.declare(c)
    CitySort = CitySort.create()
    city_consts = [getattr(CitySort, c) for c in cities]

    seg = [CitySort.Rome] + [Const(f'seg_{i}', CitySort) for i in range(1, 6)] + [CitySort.Krakow]

    for i in range(1, 6):
        s.add(Or([seg[i] == getattr(CitySort, c) for c in other_cities]))
    s.add(Distinct(seg))

    start = {getattr(CitySort, c): Int(f'start_{c}') for c in cities}
    end = {getattr(CitySort, c): Int(f'end_{c}') for c in cities}

    s.add(start[CitySort.Rome] == 1)
    s.add(end[CitySort.Rome] == 4)
    s.add(start[CitySort.Krakow] == 16)
    s.add(end[CitySort.Krakow] == 17)

    for c in other_cities:
        city_sym = getattr(CitySort, c)
        s.add(end[city_sym] - start[city_sym] + 1 == required_days[c])
        s.add(start[city_sym] >= 1)
        s.add(end[city_sym] <= 17)
        s.add(end[city_sym] >= start[city_sym])

    s.add(start[seg[0]] == 1)
    s.add(end[seg[0]] == start[seg[1]])

    for i in range(1, 6):
        s.add(end[seg[i]] == start[seg[i + 1]])

    s.add(end[seg[6]] == 17)

    for i in range(6):
        c1 = seg[i]
        c2 = seg[i + 1]
        edge_options = []
        for a, b in allowed_edges:
            a_sym = getattr(CitySort, a)
            b_sym = getattr(CitySort, b)
            edge_options.append(And(c1 == a_sym, c2 == b_sym))
        s.add(Or(edge_options))

    s.add(start[CitySort.Mykonos] <= 6)
    s.add(end[CitySort.Mykonos] >= 4)

    if s.check() == sat:
        model = s.model()
        itinerary = []
        for i in range(7):
            city_sym = model.eval(seg[i])
            city_name = None
            for c in cities:
                if model.eval(getattr(CitySort, c)) == city_sym:
                    city_name = c
                    break
            s_val = model.eval(start[city_sym]).as_long()
            e_val = model.eval(end[city_sym]).as_long()
            for d in range(s_val, e_val + 1):
                itinerary.append({"day": d, "place": city_name})
        itinerary_sorted = sorted(itinerary, key=lambda x: (x['day'], x['place'] != "Rome" and x['place'] != "Mykonos" and x['place'] != "Nice" and x['place'] != "Riga" and x['place'] != "Bucharest" and x['place'] != "Munich" and x['place'] != "Krakow"))
        result = {"itinerary": itinerary_sorted}
        print(result)
    else:
        print("No solution found")

if __name__ == "__main__":
    main()