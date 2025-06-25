from z3 import *

def main():
    cities = ["Bucharest", "Venice", "Prague", "Frankfurt", "Zurich", "Florence", "Tallinn"]
    durations = [3, 5, 4, 5, 5, 5, 5]
    city_to_index = {city: idx for idx, city in enumerate(cities)}
    
    bidirectional_pairs = [
        ("Prague", "Tallinn"),
        ("Prague", "Zurich"),
        ("Florence", "Prague"),
        ("Frankfurt", "Bucharest"),
        ("Frankfurt", "Venice"),
        ("Prague", "Bucharest"),
        ("Bucharest", "Zurich"),
        ("Tallinn", "Frankfurt"),
        ("Frankfurt", "Zurich"),
        ("Zurich", "Venice"),
        ("Florence", "Frankfurt"),
        ("Prague", "Frankfurt"),
        ("Tallinn", "Zurich")
    ]
    directed_pairs = [("Zurich", "Florence")]
    
    allowed_flights = set()
    for a, b in bidirectional_pairs:
        a_idx = city_to_index[a]
        b_idx = city_to_index[b]
        allowed_flights.add((a_idx, b_idx))
        allowed_flights.add((b_idx, a_idx))
    for a, b in directed_pairs:
        a_idx = city_to_index[a]
        b_idx = city_to_index[b]
        allowed_flights.add((a_idx, b_idx))
    
    s = Solver()
    
    order = [Int(f"order_{i}") for i in range(7)]
    for i in range(7):
        s.add(order[i] >= 0, order[i] <= 6)
    s.add(Distinct(order))
    
    base = [Int(f"base_{i}") for i in range(7)]
    s.add(base[0] == 1)
    
    for i in range(1, 7):
        expr = durations[0]
        for idx in range(1, 7):
            expr = If(order[i-1] == idx, durations[idx], expr)
        s.add(base[i] == base[i-1] + (expr - 1))
    
    last_duration = durations[0]
    for idx in range(1, 7):
        last_duration = If(order[6] == idx, durations[idx], last_duration)
    s.add(base[6] + (last_duration - 1) == 26)
    
    for k in range(6):
        constraints = []
        for (a, b) in allowed_flights:
            constraints.append(And(order[k] == a, order[k+1] == b))
        s.add(Or(constraints))
    
    venice_constraint = []
    for j in range(7):
        venice_constraint.append(And(order[j] == 1, base[j] >= 18, base[j] <= 22))
    s.add(Or(venice_constraint))
    
    frankfurt_constraint = []
    for j in range(7):
        frankfurt_constraint.append(And(order[j] == 3, base[j] >= 8, base[j] <= 16))
    s.add(Or(frankfurt_constraint))
    
    tallinn_constraint = []
    for j in range(7):
        tallinn_constraint.append(And(order[j] == 6, base[j] >= 4, base[j] <= 12))
    s.add(Or(tallinn_constraint))
    
    if s.check() == sat:
        m = s.model()
        order_vals = [m.evaluate(order[i]).as_long() for i in range(7)]
        base_vals = [m.evaluate(base[i]).as_long() for i in range(7)]
        
        itinerary = []
        for i in range(7):
            city_idx = order_vals[i]
            city = cities[city_idx]
            start = base_vals[i]
            duration_val = durations[city_idx]
            end = start + duration_val - 1
            itinerary.append({"day_range": f"Day {start}-{end}", "place": city})
            if i < 6:
                itinerary.append({"day_range": f"Day {end}", "place": city})
                next_city = cities[order_vals[i+1]]
                itinerary.append({"day_range": f"Day {end}", "place": next_city})
        
        result = {"itinerary": itinerary}
        print(result)
    else:
        print("No solution found")

if __name__ == "__main__":
    main()