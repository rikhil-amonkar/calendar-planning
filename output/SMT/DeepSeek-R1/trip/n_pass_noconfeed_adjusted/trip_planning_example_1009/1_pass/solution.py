import json
from z3 import *

def main():
    # Define cities and their indices
    cities = ["Riga", "Manchester", "Bucharest", "Florence", "Vienna", "Istanbul", "Reykjavik", "Stuttgart"]
    n_days = 23
    n_cities = len(cities)
    
    # Direct flights (bidirectional)
    direct_flights = [
        (cities.index("Bucharest"), cities.index("Vienna")),
        (cities.index("Reykjavik"), cities.index("Vienna")),
        (cities.index("Manchester"), cities.index("Vienna")),
        (cities.index("Manchester"), cities.index("Riga")),
        (cities.index("Riga"), cities.index("Vienna")),
        (cities.index("Istanbul"), cities.index("Vienna")),
        (cities.index("Vienna"), cities.index("Florence")),
        (cities.index("Stuttgart"), cities.index("Vienna")),
        (cities.index("Riga"), cities.index("Bucharest")),
        (cities.index("Istanbul"), cities.index("Riga")),
        (cities.index("Stuttgart"), cities.index("Istanbul")),
        (cities.index("Reykjavik"), cities.index("Stuttgart")),
        (cities.index("Istanbul"), cities.index("Bucharest")),
        (cities.index("Manchester"), cities.index("Istanbul")),
        (cities.index("Manchester"), cities.index("Bucharest")),
        (cities.index("Stuttgart"), cities.index("Manchester"))
    ]
    
    # Create allowed pairs set (including self-loops for non-travel)
    allowed_pairs = set()
    for i in range(n_cities):
        allowed_pairs.add((i, i))
    for (c1, c2) in direct_flights:
        allowed_pairs.add((c1, c2))
        allowed_pairs.add((c2, c1))
    
    # Initialize solver
    solver = Solver()
    
    # Create variables for each day: city1 and city2
    city1 = [Int(f"city1_{i}") for i in range(n_days)]
    city2 = [Int(f"city2_{i}") for i in range(n_days)]
    
    # Add constraints for each day: city1 and city2 must be in allowed_pairs
    for i in range(n_days):
        solver.add(Or([And(city1[i] == c1, city2[i] == c2) for (c1, c2) in allowed_pairs]))
    
    # Continuity constraint: city2[i] must equal city1[i+1] for i in 0..n_days-2
    for i in range(n_days - 1):
        solver.add(city2[i] == city1[i+1])
    
    # Event constraints
    # Istanbul must be visited on day 12 (index 11) and day 13 (index 12)
    solver.add(Or(city1[11] == cities.index("Istanbul"), city2[11] == cities.index("Istanbul")))
    solver.add(Or(city1[12] == cities.index("Istanbul"), city2[12] == cities.index("Istanbul")))
    
    # Bucharest must be visited on days 16 to 19 (indices 15 to 18)
    for i in range(15, 19):
        solver.add(Or(city1[i] == cities.index("Bucharest"), city2[i] == cities.index("Bucharest")))
    
    # Total days constraints for each city
    total_days = [0] * n_cities
    for c in range(n_cities):
        total_days[c] = Sum([If(Or(city1[i] == c, city2[i] == c), 1, 0) for i in range(n_days)])
    
    solver.add(total_days[cities.index("Riga")] == 4)
    solver.add(total_days[cities.index("Manchester")] == 5)
    solver.add(total_days[cities.index("Bucharest")] == 4)
    solver.add(total_days[cities.index("Florence")] == 4)
    solver.add(total_days[cities.index("Vienna")] == 2)
    solver.add(total_days[cities.index("Istanbul")] == 2)
    solver.add(total_days[cities.index("Reykjavik")] == 4)
    solver.add(total_days[cities.index("Stuttgart")] == 5)
    
    # Check satisfiability
    if solver.check() == sat:
        model = solver.model()
        
        # Extract the planned cities for each day
        planned_city1 = [model.evaluate(city1[i]).as_long() for i in range(n_days)]
        planned_city2 = [model.evaluate(city2[i]).as_long() for i in range(n_days)]
        
        # Create a dictionary to store days for each city
        city_days = {city: [] for city in range(n_cities)}
        for day_idx in range(n_days):
            day_num = day_idx + 1
            c1 = planned_city1[day_idx]
            c2 = planned_city2[day_idx]
            city_days[c1].append(day_num)
            if c1 != c2:
                city_days[c2].append(day_num)
        
        # Group consecutive days for each city
        itinerary_list = []
        for city_idx, days_list in city_days.items():
            if not days_list:
                continue
            days_list.sort()
            groups = []
            start = days_list[0]
            end = days_list[0]
            for day in days_list[1:]:
                if day == end + 1:
                    end = day
                else:
                    groups.append((start, end))
                    start = day
                    end = day
            groups.append((start, end))
            
            for (s, e) in groups:
                if s == e:
                    day_range_str = f"Day {s}"
                else:
                    day_range_str = f"Day {s}-{e}"
                itinerary_list.append({
                    "day_range": day_range_str,
                    "place": cities[city_idx]
                })
        
        # Sort itinerary by start day
        itinerary_list.sort(key=lambda x: int(x['day_range'].split(' ')[1].split('-')[0]))
        
        # Output as JSON
        result = {"itinerary": itinerary_list}
        print(json.dumps(result, indent=2))
    else:
        print('{"error": "No valid itinerary found"}')

if __name__ == "__main__":
    main()