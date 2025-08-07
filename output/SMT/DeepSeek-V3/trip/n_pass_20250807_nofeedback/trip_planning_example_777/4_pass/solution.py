from z3 import *

def solve_itinerary():
    # Cities
    cities = ['Dublin', 'Helsinki', 'Riga', 'Reykjavik', 'Vienna', 'Tallinn']
    city_map = {city: idx for idx, city in enumerate(cities)}
    n_days = 15

    # Direct flights: adjacency list (bidirectional)
    direct_flights = {
        'Dublin': ['Riga', 'Helsinki', 'Tallinn', 'Reykjavik', 'Vienna'],
        'Helsinki': ['Riga', 'Dublin', 'Tallinn', 'Reykjavik'],
        'Riga': ['Helsinki', 'Tallinn', 'Vienna', 'Dublin'],
        'Reykjavik': ['Vienna', 'Helsinki', 'Dublin'],
        'Vienna': ['Riga', 'Reykjavik', 'Dublin'],
        'Tallinn': ['Riga', 'Helsinki', 'Dublin']
    }

    # Create Z3 variables: for each day, which city (0..5)
    day_city = [Int(f'day_{i}_city') for i in range(n_days)]

    s = Solver()

    # Each day_city must be between 0 and 5
    for day in range(n_days):
        s.add(day_city[day] >= 0, day_city[day] < len(cities))

    # Flight constraints: transitions must be direct flights
    for day in range(n_days - 1):
        current_city = day_city[day]
        next_city = day_city[day + 1]
        # Allow staying in the same city or moving to a directly connected city
        s.add(Or(
            current_city == next_city,
            *[And(current_city == city_map[a], next_city == city_map[b]) 
              for a in direct_flights for b in direct_flights[a]]
        ))

    # Duration constraints
    # Dublin: 5 days total
    s.add(Sum([If(day_city[i] == city_map['Dublin'], 1, 0) for i in range(n_days)]) == 5)
    # Helsinki: 3 days total
    s.add(Sum([If(day_city[i] == city_map['Helsinki'], 1, 0) for i in range(n_days)]) == 3)
    # Riga: 3 days
    s.add(Sum([If(day_city[i] == city_map['Riga'], 1, 0) for i in range(n_days)]) == 3)
    # Reykjavik: 2 days
    s.add(Sum([If(day_city[i] == city_map['Reykjavik'], 1, 0) for i in range(n_days)]) == 2)
    # Vienna: 2 days
    s.add(Sum([If(day_city[i] == city_map['Vienna'], 1, 0) for i in range(n_days)]) == 2)
    # Tallinn: 5 days
    s.add(Sum([If(day_city[i] == city_map['Tallinn'], 1, 0) for i in range(n_days)]) == 5)

    # Event constraints
    # Vienna show between day 2 and 3 (0-based: days 1 and 2)
    s.add(Or(day_city[1] == city_map['Vienna'], day_city[2] == city_map['Vienna']))
    # Friends in Helsinki between day 3 and 5 (0-based: days 2,3,4)
    s.add(Or([day_city[i] == city_map['Helsinki'] for i in range(2, 5)]))
    # Wedding in Tallinn between day 7 and 11 (0-based: days 6..10)
    s.add(Or([day_city[i] == city_map['Tallinn'] for i in range(6, 11)]))

    # Check and get model
    if s.check() == sat:
        m = s.model()
        itinerary = []
        for day in range(n_days):
            city_idx = m.evaluate(day_city[day]).as_long()
            itinerary.append({"day": day + 1, "city": cities[city_idx]})
        return {"itinerary": itinerary}
    else:
        return {"error": "No valid itinerary found"}

# Run the solver and print the result
result = solve_itinerary()
import json
print(json.dumps(result, indent=2))