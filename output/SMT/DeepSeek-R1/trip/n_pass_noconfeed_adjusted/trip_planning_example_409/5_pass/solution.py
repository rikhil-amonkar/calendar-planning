from z3 import *
import json

def main():
    # Define the cities
    City, (Zurich, Hamburg, Helsinki, Bucharest, Split) = EnumSort('City', ['Zurich', 'Hamburg', 'Helsinki', 'Bucharest', 'Split'])
    cities = [Zurich, Hamburg, Helsinki, Bucharest, Split]
    city_names = {Zurich: 'Zurich', Hamburg: 'Hamburg', Helsinki: 'Helsinki', Bucharest: 'Bucharest', Split: 'Split'}
    
    # Create a mapping from city to index
    city_to_index = {city: idx for idx, city in enumerate(cities)}
    
    # Direct flights (bidirectional)
    direct_flights = [
        (Zurich, Helsinki),
        (Hamburg, Bucharest),
        (Helsinki, Hamburg),
        (Zurich, Hamburg),
        (Zurich, Bucharest),
        (Zurich, Split),
        (Helsinki, Split),
        (Split, Hamburg)
    ]
    
    # Initialize adjacency matrix with direct flights (bidirectional)
    n = len(cities)
    adj = [[False] * n for _ in range(n)]
    for (a, b) in direct_flights:
        i = city_to_index[a]
        j = city_to_index[b]
        adj[i][j] = True
        adj[j][i] = True
    
    # Create extended flights (direct or one layover)
    extended_flights = set()
    for i in range(n):
        for j in range(n):
            if i == j:
                continue
            if adj[i][j]:
                extended_flights.add((cities[i], cities[j]))
            else:
                for k in range(n):
                    if adj[i][k] and adj[k][j]:
                        extended_flights.add((cities[i], cities[j]))
                        break
    
    # Create arrays for start_city and end_city for 12 days (index 0 to 11代表 day1 to day12)
    start_city = [Const(f'start_city_{i}', City) for i in range(12)]
    end_city = [Const(f'end_city_{i}', City) for i in range(12)]
    
    s = Solver()
    
    # Constraint: Start in Zurich on Day 1
    s.add(start_city[0] == Zurich)
    # Constraint: End in Split on Day 12
    s.add(end_city[11] == Split)
    
    # Constraint: For i in 0 to 10, end_city[i] equals start_city[i+1]
    for i in range(11):
        s.add(end_city[i] == start_city[i+1])
    
    # Constraint: If start_city[i] != end_city[i], then there must be a direct or indirect flight
    for i in range(12):
        a = start_city[i]
        b = end_city[i]
        # If staying in the same city, no flight needed
        s.add(If(a != b, Or([And(a == c1, b == c2) for (c1, c2) in extended_flights]), True))
    
    # Function to count days in a city
    def count_city(c):
        total = 0
        for i in range(12):
            # Count start city
            total += If(start_city[i] == c, 1, 0)
            # Count end city only if it's a travel day (start != end)
            total += If(And(end_city[i] == c, start_city[i] != end_city[i]), 1, 0)
        return total
    
    # City day constraints
    s.add(count_city(Hamburg) == 2)
    s.add(count_city(Zurich) == 3)
    s.add(count_city(Helsinki) == 2)
    s.add(count_city(Bucharest) == 2)
    s.add(count_city(Split) == 7)
    
    # Conference constraints: Must be in Split all day on day4 and day10
    s.add(start_city[3] == Split)  # day4
    s.add(end_city[3] == Split)    # day4
    s.add(start_city[9] == Split)  # day10
    s.add(end_city[9] == Split)    # day10
    
    # Wedding constraint: Must be in Zurich on at least one of day1, day2, or day3
    wedding_days = []
    for i in range(3):
        # Either start in Zurich or travel to Zurich on that day
        wedding_days.append(Or(start_city[i] == Zurich, 
                              And(start_city[i] != end_city[i], end_city[i] == Zurich)))
    s.add(Or(wedding_days))
    
    # Check for a solution
    if s.check() == sat:
        m = s.model()
        # Extract the start_city for each day
        start_city_values = [m.evaluate(start_city[i]) for i in range(12)]
        start_city_str = [city_names[city] for city in start_city_values]
        
        # Generate itinerary segments
        itinerary = []
        current_city = start_city_str[0]
        start_day = 1
        for day_index in range(1, 12):
            if start_city_str[day_index] != current_city:
                end_day = day_index
                itinerary.append({"day_range": f"Day {start_day}-{end_day}", "place": current_city})
                current_city = start_city_str[day_index]
                start_day = day_index + 1
        itinerary.append({"day_range": f"Day {start_day}-12", "place": current_city})
        
        # Output as JSON
        print(json.dumps({"itinerary": itinerary}))
    else:
        print('{"itinerary": []}')

if __name__ == "__main__":
    main()