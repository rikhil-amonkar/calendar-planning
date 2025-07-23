import z3

def main():
    days = list(range(1, 18))
    cities = ["Warsaw", "Budapest", "Paris", "Riga"]
    
    adjacent_pairs = {
        frozenset(("Warsaw", "Budapest")),
        frozenset(("Warsaw", "Riga")),
        frozenset(("Warsaw", "Paris")),
        frozenset(("Budapest", "Paris")),
        frozenset(("Paris", "Riga"))
    }
    
    neighbors = {
        "Warsaw": ["Budapest", "Riga", "Paris"],
        "Budapest": ["Warsaw", "Paris"],
        "Paris": ["Warsaw", "Budapest", "Riga"],
        "Riga": ["Warsaw", "Paris"]
    }
    
    in_city = {}
    for d in days:
        for c in cities:
            in_city[(d, c)] = z3.Bool(f"in_city_{d}_{c}")
    
    s = z3.Solver()
    
    for d in days:
        s.add(z3.Or([in_city[(d, c)] for c in cities]))
        city_bools = [in_city[(d, c)] for c in cities]
        s.add(z3.AtMost(*city_bools, 2))
        
        for i in range(len(cities)):
            for j in range(i+1, len(cities)):
                c1 = cities[i]
                c2 = cities[j]
                if frozenset([c1, c2]) not in adjacent_pairs:
                    s.add(z3.Not(z3.And(in_city[(d, c1)], in_city[(d, c2)])))
    
    s.add(in_city[(1, "Warsaw")])
    for c in cities:
        if c != "Warsaw":
            s.add(z3.Not(in_city[(1, c)]))
    
    s.add(in_city[(2, "Warsaw")])
    
    for d in range(1, 11):
        s.add(z3.Not(in_city[(d, "Riga")]))
    for d in range(11, 18):
        s.add(in_city[(d, "Riga")])
    
    for d in range(3, 18):
        s.add(z3.Not(in_city[(d, "Warsaw")]))
    
    budapest_days = [z3.If(in_city[(d, "Budapest")], 1, 0) for d in days]
    s.add(sum(budapest_days) == 7)
    
    paris_days = [z3.If(in_city[(d, "Paris")], 1, 0) for d in days]
    s.add(sum(paris_days) == 4)
    
    for d in range(2, 18):
        for c in cities:
            current = in_city[(d, c)]
            prev = in_city[(d-1, c)]
            neighbor_conds = []
            for c0 in neighbors[c]:
                neighbor_conds.append(z3.And(in_city[(d-1, c0)], in_city[(d, c0)]))
            if neighbor_conds:
                s.add(z3.Implies(z3.And(current, z3.Not(prev)), z3.Or(neighbor_conds)))
    
    if s.check() == z3.sat:
        m = s.model()
        itinerary = []
        for d in days:
            for c in cities:
                if m.evaluate(in_city[(d, c)]):
                    itinerary.append({"day": d, "city": c})
        result = {"itinerary": itinerary}
        print(result)
    else:
        print("No solution found")

if __name__ == "__main__":
    main()