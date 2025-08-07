from z3 import *
import json

def main():
    cities = ["Mykonos", "Nice", "London", "Copenhagen", "Oslo", "Tallinn"]
    flight_edges = [
        ("London", "Copenhagen"),
        ("Copenhagen", "Tallinn"),
        ("Tallinn", "Oslo"),
        ("Mykonos", "London"),
        ("Oslo", "Nice"),
        ("London", "Nice"),
        ("Mykonos", "Nice"),
        ("London", "Oslo"),
        ("Copenhagen", "Nice"),
        ("Copenhagen", "Oslo")
    ]
    
    allowed_pairs = set()
    for u, v in flight_edges:
        allowed_pairs.add(frozenset({u, v}))
    
    in_city = {}
    for c in cities:
        for d in range(1, 17):
            in_city[(c, d)] = Bool(f"in_{c}_{d}")
    
    s = Solver()
    
    for d in range(1, 17):
        s.add(Or([in_city[(c, d)] for c in cities]))
        for i in range(len(cities)):
            for j in range(i+1, len(cities)):
                for k in range(j+1, len(cities)):
                    c1, c2, c3 = cities[i], cities[j], cities[k]
                    s.add(Not(And(in_city[(c1, d)], in_city[(c2, d)], in_city[(c3, d)])))
    
    for d in range(1, 17):
        for i in range(len(cities)):
            for j in range(i+1, len(cities)):
                c1, c2 = cities[i], cities[j]
                if frozenset({c1, c2}) not in allowed_pairs:
                    s.add(Not(And(in_city[(c1, d)], in_city[(c2, d)])))
    
    for d in range(1, 16):
        s.add(Or([And(in_city[(c, d)], in_city[(c, d+1)]) for c in cities]))
    
    counts = {
        "Mykonos": 4,
        "Nice": 3,
        "London": 2,
        "Copenhagen": 3,
        "Oslo": 5,
        "Tallinn": 4
    }
    for city, total_days in counts.items():
        s.add(Sum([If(in_city[(city, d)], 1, 0) for d in range(1, 17)]) == total_days)
    
    s.add(in_city[("Nice", 14)])
    s.add(in_city[("Nice", 16)])
    s.add(Or([in_city[("Oslo", d)] for d in range(10, 15)]))
    
    if s.check() == sat:
        m = s.model()
        itinerary = []
        for d in range(1, 17):
            cities_today = []
            for c in cities:
                if m.evaluate(in_city[(c, d)]):
                    cities_today.append(c)
            cities_today.sort()
            if len(cities_today) == 1:
                city_str = cities_today[0]
            else:
                city_str = ", ".join(cities_today)
            itinerary.append({"day": d, "city": city_str})
        
        result = {"itinerary": itinerary}
        print(json.dumps(result, indent=2))
    else:
        print('{"itinerary": []}')
        print("No solution found", file=sys.stderr)

if __name__ == "__main__":
    main()