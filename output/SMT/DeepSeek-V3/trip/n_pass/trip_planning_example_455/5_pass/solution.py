from z3 import *

def solve_itinerary():
    # Cities and their indices
    cities = ['Reykjavik', 'Riga', 'Warsaw', 'Istanbul', 'Krakow']
    Reykjavik, Riga, Warsaw, Istanbul, Krakow = 0, 1, 2, 3, 4
    num_cities = len(cities)
    num_days = 21

    # Direct flights adjacency list (bidirectional)
    direct_flights = [
        (Reykjavik, Warsaw),
        (Riga, Istanbul),
        (Riga, Warsaw),
        (Warsaw, Istanbul),
        (Warsaw, Krakow),
        (Istanbul, Krakow)
    ]

    # Create Z3 solver
    s = Solver()

    # Decision variables: day[i] represents the city on day i+1 (1-based)
    day = [Int(f"day_{i+1}") for i in range(num_days)]

    # Each day must be assigned to a valid city
    for d in day:
        s.add(And(d >= 0, d < num_cities))

    # Flight connection constraints between consecutive days
    for i in range(num_days - 1):
        current = day[i]
        next_day = day[i + 1]
        # Either stay in same city or take a direct flight
        s.add(Or(
            current == next_day,
            *[And(current == c1, next_day == c2) for (c1, c2) in direct_flights],
            *[And(current == c2, next_day == c1) for (c1, c2) in direct_flights]
        ))

    # Calculate days spent in each city
    days_in_city = [Sum([If(day[i] == c, 1, 0) for i in range(num_days)]) 
                   for c in range(num_cities)]

    # Required days in each city
    s.add(days_in_city[Reykjavik] == 7)
    s.add(days_in_city[Riga] == 2)
    s.add(days_in_city[Warsaw] == 3)
    s.add(days_in_city[Istanbul] == 6)
    s.add(days_in_city[Krakow] == 7)

    # Special constraints
    # Must be in Riga on day 1 or 2
    s.add(Or(day[0] == Riga, day[1] == Riga))
    
    # Must be in Istanbul between days 2-7 (indices 1-6)
    s.add(Or([day[i] == Istanbul for i in range(1, 7)]))

    # Try to find a solution
    if s.check() == sat:
        m = s.model()
        itinerary = []
        for i in range(num_days):
            city_idx = m.evaluate(day[i]).as_long()
            itinerary.append({"day": i+1, "place": cities[city_idx]})
        
        return {"itinerary": itinerary}
    else:
        return {"error": "No valid itinerary found"}

# Run and print the result
import json
result = solve_itinerary()
print(json.dumps(result, indent=2))