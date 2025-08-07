from z3 import *
import json

def main():
    cities = ["Zurich", "Hamburg", "Helsinki", "Bucharest", "Split"]
    city_to_int = {name: idx for idx, name in enumerate(cities)}
    
    undirected_edges = [
        ("Zurich", "Helsinki"),
        ("Hamburg", "Bucharest"),
        ("Helsinki", "Hamburg"),
        ("Zurich", "Hamburg"),
        ("Zurich", "Bucharest"),
        ("Zurich", "Split"),
        ("Helsinki", "Split"),
        ("Split", "Hamburg")
    ]
    
    directed_edges = []
    for u, v in undirected_edges:
        u_idx = city_to_int[u]
        v_idx = city_to_int[v]
        directed_edges.append((u_idx, v_idx))
        directed_edges.append((v_idx, u_idx))
    
    required_days = [3, 2, 2, 2, 7]
    zurich = city_to_int["Zurich"]
    split = city_to_int["Split"]
    
    s = Solver()
    
    # Start city for each day (S0 = start of day1, S1 = start of day2, etc.)
    S = [Int(f'S_{i}') for i in range(12)]
    for i in range(12):
        s.add(S[i] >= 0, S[i] < 5)
    
    # Flight constraints between consecutive days
    for i in range(11):
        current_city = S[i]
        next_city = S[i+1]
        # If changing cities, ensure direct flight exists
        s.add(If(current_city != next_city,
                 Or([And(current_city == u, next_city == v) for (u, v) in directed_edges]),
                 True))
    
    # Wedding constraint: must be in Zurich on at least one of days 1-3
    s.add(Or(S[0] == zurich, S[1] == zurich, S[2] == zurich))
    
    # Conference constraints: must be in Split on day4 and day10
    s.add(S[3] == split)  # Day4
    s.add(S[9] == split)  # Day10
    
    # Total days per city
    for c in range(5):
        total = 0
        for i in range(12):
            total += If(S[i] == c, 1, 0)
        s.add(total == required_days[c])
    
    if s.check() == sat:
        model = s.model()
        start_cities = [model.evaluate(S[i]).as_long() for i in range(12)]
        
        # Build itinerary by grouping consecutive days in the same city
        itinerary = []
        current_city = start_cities[0]
        start_day = 1
        for day in range(1, 12):
            if start_cities[day] != current_city:
                itinerary.append({
                    'day_range': f'Day {start_day}-{day}',
                    'place': cities[current_city]
                })
                current_city = start_cities[day]
                start_day = day + 1
        itinerary.append({
            'day_range': f'Day {start_day}-12',
            'place': cities[current_city]
        })
        
        result = {"itinerary": itinerary}
        print(json.dumps(result, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()