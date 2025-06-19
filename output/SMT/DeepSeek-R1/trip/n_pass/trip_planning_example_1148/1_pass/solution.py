from z3 import *

def main():
    cities = ["Lisbon", "Dubrovnik", "Copenhagen", "Prague", "Tallinn", "Stockholm", "Split", "Lyon"]
    required_days = [2, 5, 5, 3, 2, 4, 3, 2]
    city_to_index = {city: idx for idx, city in enumerate(cities)}
    
    direct_flights = [
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
    
    allowed_pairs = set()
    for city1, city2 in direct_flights:
        idx1 = city_to_index[city1]
        idx2 = city_to_index[city2]
        allowed_pairs.add((min(idx1, idx2), max(idx1, idx2)))
    
    s = [Int(f's_{i}') for i in range(8)]
    e = [Int(f'e_{i}') for i in range(8)]
    order = [Int(f'order_{i}') for i in range(8)]
    
    solver = Solver()
    
    for i in range(8):
        solver.add(s[i] >= 1)
        solver.add(e[i] <= 19)
        solver.add(e[i] == s[i] + required_days[i] - 1)
    
    solver.add(Distinct(order))
    for i in range(8):
        solver.add(order[i] >= 0)
        solver.add(order[i] < 8)
    
    solver.add(order[7] == city_to_index["Lyon"])
    
    solver.add(s[order[0]] == 1)
    
    for i in range(7):
        solver.add(e[order[i]] == s[order[i+1]])
    
    solver.add(s[city_to_index["Lisbon"]] <= 5)
    solver.add(e[city_to_index["Lisbon"]] >= 4)
    
    solver.add(s[city_to_index["Tallinn"]] <= 2)
    solver.add(e[city_to_index["Tallinn"]] >= 1)
    
    solver.add(s[city_to_index["Stockholm"]] <= 16)
    solver.add(e[city_to_index["Stockholm"]] >= 13)
    
    solver.add(s[city_to_index["Lyon"]] == 18)
    solver.add(e[city_to_index["Lyon"]] == 19)
    
    for i in range(7):
        x = order[i]
        y = order[i+1]
        constraints = []
        for pair in allowed_pairs:
            a, b = pair
            constraints.append(Or(And(x == a, y == b), And(x == b, y == a)))
        solver.add(Or(constraints))
    
    if solver.check() == sat:
        model = solver.model()
        order_vals = [model.eval(order[i]).as_long() for i in range(8)]
        s_vals = [model.eval(s[i]).as_long() for i in range(8)]
        e_vals = [model.eval(e[i]).as_long() for i in range(8)]
        
        itinerary = []
        for i in range(8):
            city_idx = order_vals[i]
            city = cities[city_idx]
            start_val = s_vals[city_idx]
            end_val = e_vals[city_idx]
            itinerary.append({"day_range": f"Day {start_val}-{end_val}", "place": city})
            if i < 7:
                next_city_idx = order_vals[i+1]
                next_city = cities[next_city_idx]
                itinerary.append({"day_range": f"Day {end_val}", "place": city})
                itinerary.append({"day_range": f"Day {end_val}", "place": next_city})
        
        result = {"itinerary": itinerary}
        print(result)
    else:
        print("No solution found")

if __name__ == "__main__":
    main()