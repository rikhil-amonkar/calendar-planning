from z3 import *
import json

def main():
    cities = ["Dubrovnik", "Lisbon", "Copenhagen", "Prague", "Tallinn", "Stockholm", "Split", "Lyon"]
    given_edges = [
        ("Dubrovnik", "Stockholm"),
        ("Lisbon", "Copenhagen"),
        ("Lisbon", "Lyon"),
        ("Copenhagen", "Stockholm"),
        ("Copenhagen", "Split"),
        ("Prague", "Stockholm"),
        ("Tallinn", "Stockholm"),
        ("Prague", "Lyon"),
        ("Lisbon", "Stockholm"),
        ("Prague", "Lisbon"),
        ("Stockholm", "Split"),
        ("Prague", "Copenhagen"),
        ("Split", "Lyon"),
        ("Copenhagen", "Dubrovnik"),
        ("Prague", "Split"),
        ("Tallinn", "Copenhagen"),
        ("Tallinn", "Prague")
    ]
    edges_set = set()
    for u, v in given_edges:
        edges_set.add(frozenset([u, v]))
    
    s = Solver()
    days_range = list(range(1, 20))
    flight = {d: Bool(f'flight_{d}') for d in range(1, 19)}
    in_city = {}
    for d in range(1, 20):
        for city in cities:
            in_city[(d, city)] = Bool(f'in_{d}_{city}')
    
    for d in range(1, 20):
        cities_today = [in_city[(d, city)] for city in cities]
        if d < 19:
            s.add(If(flight[d],
                     Sum([If(c, 1, 0) for c in cities_today]) == 2,
                     Sum([If(c, 1, 0) for c in cities_today]) == 1))
        else:
            s.add(Sum([If(c, 1, 0) for c in cities_today]) == 1)
    
    for d in range(1, 19):
        common_city = Or([And(in_city[(d, city)], in_city[(d+1, city)]) for city in cities])
        s.add(common_city)
    
    for d in range(1, 19):
        for u in cities:
            for v in cities:
                if u != v and frozenset([u, v]) not in edges_set:
                    s.add(Or(Not(flight[d]), Not(in_city[(d, u)]), Not(in_city[(d, v)])))
    
    total_days = {}
    for city in cities:
        total = 0
        for d in range(1, 20):
            total += If(in_city[(d, city)], 1, 0)
        total_days[city] = total
    s.add(total_days["Lisbon"] == 2)
    s.add(total_days["Dubrovnik"] == 5)
    s.add(total_days["Copenhagen"] == 5)
    s.add(total_days["Prague"] == 3)
    s.add(total_days["Tallinn"] == 2)
    s.add(total_days["Stockholm"] == 4)
    s.add(total_days["Split"] == 3)
    s.add(total_days["Lyon"] == 2)
    
    s.add(Or(in_city[(4, "Lisbon")], in_city[(5, "Lisbon")]))
    s.add(Or(in_city[(1, "Tallinn")], in_city[(2, "Tallinn")]))
    s.add(Or([in_city[(d, "Stockholm")] for d in [13, 14, 15, 16]]))
    s.add(And(in_city[(18, "Lyon")], in_city[(19, "Lyon")]))
    
    if s.check() == sat:
        m = s.model()
        presence = {}
        for d in range(1, 20):
            for city in cities:
                presence[(d, city)] = m.evaluate(in_city[(d, city)])
        flight_days = []
        for d in range(1, 19):
            if m.evaluate(flight[d]):
                flight_days.append(d)
        
        records = []
        for city in cities:
            days_list = [d for d in range(1, 20) if presence.get((d, city), False)]
            if not days_list:
                continue
            intervals = []
            start = days_list[0]
            end = start
            for i in range(1, len(days_list)):
                if days_list[i] == end + 1:
                    end = days_list[i]
                else:
                    intervals.append((start, end))
                    start = days_list[i]
                    end = days_list[i]
            intervals.append((start, end))
            for (s, e) in intervals:
                day_range_str = f"Day {s}" if s == e else f"Day {s}-{e}"
                records.append((s, e, 1, city, day_range_str))
        
        for d in flight_days:
            for city in cities:
                if presence.get((d, city), False):
                    records.append((d, d, 0, city, f"Day {d}"))
        
        records_sorted = sorted(records, key=lambda x: (x[0], x[2], x[1], x[3]))
        itinerary = [{"day_range": r[4], "place": r[3]} for r in records_sorted]
        result = {"itinerary": itinerary}
        print(json.dumps(result, indent=2))
    else:
        print("No solution found")

if __name__ == '__main__':
    main()