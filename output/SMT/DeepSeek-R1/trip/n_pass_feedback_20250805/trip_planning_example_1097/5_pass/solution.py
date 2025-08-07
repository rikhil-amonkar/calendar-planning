from z3 import *
import json

def main():
    cities = ['Reykjavik', 'Riga', 'Oslo', 'Lyon', 'Dubrovnik', 'Madrid', 'Warsaw', 'London']
    city_to_idx = {city: idx for idx, city in enumerate(cities)}
    required_days = [4, 2, 3, 5, 2, 2, 4, 3]
    
    edges = [
        (0, 6), (2, 5), (6, 1), (3, 7), (5, 7), (6, 7), (0, 5), (6, 2), (2, 4),
        (0, 2), (1, 2), (2, 3), (2, 7), (0, 7), (6, 5), (5, 3), (4, 5)
    ]
    flights_set = set()
    for a, b in edges:
        flights_set.add((min(a, b), max(a, b)))
    
    n_days = 18
    n_cities = len(cities)
    s = Solver()
    
    # Start and end cities for each day
    start = [Int(f'start_{i}') for i in range(n_days)]
    end = [Int(f'end_{i}') for i in range(n_days)]
    
    # Constraint: Cities are valid indices
    for i in range(n_days):
        s.add(start[i] >= 0, start[i] < n_cities)
        s.add(end[i] >= 0, end[i] < n_cities)
    
    # Start in Warsaw and end in Lyon
    s.add(start[0] == city_to_idx['Warsaw'])
    s.add(end[n_days-1] == city_to_idx['Lyon'])
    
    # Continuity between days: end of previous day is start of current day
    for i in range(1, n_days):
        s.add(end[i-1] == start[i])
    
    # Flight constraints: Either stay in same city or take direct flight
    for i in range(n_days):
        stay = (start[i] == end[i])
        flight = Or([And(start[i] == a, end[i] == b) for a, b in flights_set] + 
                   [And(start[i] == b, end[i] == a) for a, b in flights_set])
        s.add(Or(stay, flight))
    
    # Count days in each city
    for c in range(n_cities):
        total = 0
        for i in range(n_days):
            # Count start city if it matches
            total += If(start[i] == c, 1, 0)
            # Count end city only if different from start (travel day)
            total += If(And(start[i] != end[i], end[i] == c), 1, 0)
        s.add(total == required_days[c])
    
    # Must be in Riga on day 4 or 5
    s.add(Or(
        start[3] == city_to_idx['Riga'], end[3] == city_to_idx['Riga'],
        start[4] == city_to_idx['Riga'], end[4] == city_to_idx['Riga']
    ))
    
    # Must be in Dubrovnik on day 7 or 8
    s.add(Or(
        start[6] == city_to_idx['Dubrovnik'], end[6] == city_to_idx['Dubrovnik'],
        start[7] == city_to_idx['Dubrovnik'], end[7] == city_to_idx['Dubrovnik']
    ))
    
    if s.check() == sat:
        m = s.model()
        start_cities = []
        end_cities = []
        for i in range(n_days):
            sc = m.evaluate(start[i]).as_long()
            ec = m.evaluate(end[i]).as_long()
            start_cities.append(cities[sc])
            end_cities.append(cities[ec])
        
        itinerary = []
        i = 0
        while i < n_days:
            if start_cities[i] != end_cities[i]:
                # Travel day: single day with two cities
                itinerary.append({
                    "day_range": f"Day {i+1}",
                    "place": f"{start_cities[i]}, {end_cities[i]}"
                })
                i += 1
            else:
                # Non-travel day: merge consecutive days in same city
                city = start_cities[i]
                j = i
                while j < n_days and start_cities[j] == city and end_cities[j] == city:
                    j += 1
                if i + 1 == j:
                    day_range_str = f"Day {i+1}"
                else:
                    day_range_str = f"Day {i+1}-{j}"
                itinerary.append({
                    "day_range": day_range_str,
                    "place": city
                })
                i = j
        
        print(json.dumps({"itinerary": itinerary}))
    else:
        print("No solution found")

if __name__ == '__main__':
    main()