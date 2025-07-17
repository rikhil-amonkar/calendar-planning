import z3

def main():
    cities = ["Venice", "Barcelona", "Copenhagen", "Lyon", "Reykjavik", "Dubrovnik", "Athens", "Tallinn", "Munich"]
    durations = {
        "Venice": 4,
        "Barcelona": 3,
        "Copenhagen": 4,
        "Lyon": 4,
        "Reykjavik": 4,
        "Dubrovnik": 5,
        "Athens": 2,
        "Tallinn": 5,
        "Munich": 3
    }
    
    edges_list = [
        ("Copenhagen", "Athens"),
        ("Copenhagen", "Dubrovnik"),
        ("Munich", "Tallinn"),
        ("Copenhagen", "Munich"),
        ("Venice", "Munich"),
        ("Reykjavik", "Athens"),
        ("Athens", "Dubrovnik"),
        ("Venice", "Athens"),
        ("Lyon", "Barcelona"),
        ("Copenhagen", "Reykjavik"),
        ("Reykjavik", "Munich"),
        ("Athens", "Munich"),
        ("Lyon", "Munich"),
        ("Barcelona", "Reykjavik"),
        ("Venice", "Copenhagen"),
        ("Barcelona", "Dubrovnik"),
        ("Lyon", "Venice"),
        ("Dubrovnik", "Munich"),
        ("Barcelona", "Athens"),
        ("Copenhagen", "Barcelona"),
        ("Venice", "Barcelona"),
        ("Barcelona", "Munich"),
        ("Barcelona", "Tallinn"),
        ("Copenhagen", "Tallinn")
    ]
    
    edge_set_sym = set()
    for u, v in edges_list:
        key = (min(u, v), max(u, v))
        edge_set_sym.add(key)
    
    positions = { city: z3.Int(f'pos_{city}') for city in cities }
    starts = { city: z3.Int(f'start_{city}') for city in cities }
    ends = { city: z3.Int(f'end_{city}') for city in cities }
    
    s = z3.Solver()
    
    # Positions are distinct and between 0 and 8
    s.add(z3.Distinct([positions[c] for c in cities]))
    for c in cities:
        s.add(positions[c] >= 0, positions[c] <= 8)
    
    # Duration constraints
    for c in cities:
        s.add(ends[c] == starts[c] + durations[c] - 1)
    
    # Flight constraints: if two cities are not connected, they cannot be consecutive
    for i in range(len(cities)):
        for j in range(i+1, len(cities)):
            c1 = cities[i]
            c2 = cities[j]
            key = (min(c1, c2), max(c1, c2))
            if key not in edge_set_sym:
                cond = z3.Or(
                    positions[c1] == positions[c2] + 1,
                    positions[c1] == positions[c2] - 1
                )
                s.add(z3.Not(cond))
    
    # Consecutive cities in sequence must have end_i = start_j
    for c1 in cities:
        for c2 in cities:
            if c1 == c2:
                continue
            cond = (positions[c2] == positions[c1] + 1)
            s.add(z3.Implies(cond, ends[c1] == starts[c2]))
    
    # First city starts at 1, last ends at 26
    for c in cities:
        s.add(z3.Implies(positions[c] == 0, starts[c] == 1))
        s.add(z3.Implies(positions[c] == 8, ends[c] == 26))
    
    # Event constraints
    s.add(starts["Barcelona"] <= 12, ends["Barcelona"] >= 10)
    s.add(starts["Copenhagen"] <= 10, ends["Copenhagen"] >= 7)
    s.add(starts["Dubrovnik"] <= 20, ends["Dubrovnik"] >= 16)
    
    if s.check() == z3.sat:
        m = s.model()
        pos_vals = { c: m.evaluate(positions[c]).as_long() for c in cities }
        start_vals = { c: m.evaluate(starts[c]).as_long() for c in cities }
        end_vals = { c: m.evaluate(ends[c]).as_long() for c in cities }
        
        sorted_cities = sorted(cities, key=lambda c: pos_vals[c])
        
        itinerary = []
        for i, c in enumerate(sorted_cities):
            start = start_vals[c]
            end = end_vals[c]
            if start == end:
                day_range = f"Day {start}"
            else:
                day_range = f"Day {start}-{end}"
            itinerary.append({"day_range": day_range, "place": c})
            
            if i < len(sorted_cities) - 1:
                flight_day = end
                next_c = sorted_cities[i+1]
                itinerary.append({"day_range": f"Day {flight_day}", "place": c})
                itinerary.append({"day_range": f"Day {flight_day}", "place": next_c})
        
        result = {"itinerary": itinerary}
        print(result)
    else:
        print("No solution found")

if __name__ == "__main__":
    main()