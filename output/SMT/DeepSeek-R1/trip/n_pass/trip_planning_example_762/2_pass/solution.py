from z3 import *
import json

def main():
    cities = ['Dublin', 'Madrid', 'Oslo', 'London', 'Vilnius', 'Berlin']
    required_days = {
        'Dublin': 3,
        'Madrid': 2,
        'Oslo': 3,
        'London': 2,
        'Vilnius': 3,
        'Berlin': 5
    }
    
    events = {
        'Dublin': [7, 8, 9],
        'Madrid': [2, 3],
        'Berlin': [3, 4, 5, 6, 7]
    }
    
    flight_list_str = [
        "London and Madrid",
        "Oslo and Vilnius",
        "Berlin and Vilnius",
        "Madrid and Oslo",
        "Madrid and Dublin",
        "London and Oslo",
        "Madrid and Berlin",
        "Berlin and Oslo",
        "Dublin and Oslo",
        "London and Dublin",
        "London and Berlin",
        "Berlin and Dublin"
    ]
    
    flight_pairs = set()
    for s in flight_list_str:
        a, b = s.split(' and ')
        flight_pairs.add((min(a, b), max(a, b)))
    
    days = list(range(1, 14))
    x = {}
    for d in days:
        x[d] = {}
        for c in cities:
            x[d][c] = Bool(f"x_{d}_{c}")
    
    s = Solver()
    
    for d in days:
        s.add(Or([x[d][c] for c in cities]))
        for i in range(len(cities)):
            for j in range(i+1, len(cities)):
                for k in range(j+1, len(cities)):
                    c1, c2, c3 = cities[i], cities[j], cities[k]
                    s.add(Not(And(x[d][c1], x[d][c2], x[d][c3])))
    
    for c in cities:
        total = Sum([If(x[d][c], 1, 0) for d in days])
        s.add(total == required_days[c])
    
    for d in days:
        for i in range(len(cities)):
            for j in range(i+1, len(cities)):
                c1 = cities[i]
                c2 = cities[j]
                pair = (min(c1, c2), max(c1, c2))
                s.add(Implies(And(x[d][c1], x[d][c2]), pair in flight_pairs))
    
    for c in cities:
        for d in range(1, 13):
            cond = And(x[d][c], Not(x[d+1][c]))
            other_cities = [c2 for c2 in cities if c2 != c and (min(c, c2), max(c, c2)) in flight_pairs]
            if other_cities:
                s.add(Implies(cond, Or([x[d][c2] for c2 in other_cities])))
            else:
                s.add(Not(cond))
    
    for city, event_days in events.items():
        s.add(Or([x[d][city] for d in event_days]))
    
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for d in days:
            for c in cities:
                if is_true(model.eval(x[d][c])):
                    itinerary.append({"day": d, "city": c})
        result = {"itinerary": itinerary}
        print(json.dumps(result, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()