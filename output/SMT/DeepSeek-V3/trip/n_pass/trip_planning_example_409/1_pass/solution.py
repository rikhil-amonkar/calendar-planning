from z3 import *

def solve_itinerary():
    # Define the cities
    cities = ['Zurich', 'Hamburg', 'Helsinki', 'Bucharest', 'Split']
    city_vars = {city: Int(city) for city in cities}
    
    # Days are from 1 to 12
    days = 12
    # Create a solver instance
    s = Solver()
    
    # For each day, which city are we in?
    day_to_city = [Int(f'day_{i}') for i in range(1, days + 1)]
    
    # Map cities to integers for the solver
    city_map = {city: idx for idx, city in enumerate(cities)}
    city_inv_map = {idx: city for idx, city in enumerate(cities)}
    
    # Constraints for each day's variable to be a valid city index
    for day_var in day_to_city:
        s.add(day_var >= 0, day_var < len(cities))
    
    # Direct flights: adjacency list
    direct_flights = {
        'Zurich': ['Helsinki', 'Hamburg', 'Bucharest', 'Split'],
        'Hamburg': ['Zurich', 'Bucharest', 'Helsinki', 'Split'],
        'Helsinki': ['Zurich', 'Hamburg', 'Split'],
        'Bucharest': ['Zurich', 'Hamburg'],
        'Split': ['Zurich', 'Helsinki', 'Hamburg']
    }
    
    # Ensure transitions between cities are via direct flights
    for i in range(days - 1):
        current_day_var = day_to_city[i]
        next_day_var = day_to_city[i + 1]
        # Either stay in the same city or move to a directly connected city
        s.add(Or(
            current_day_var == next_day_var,
            *[
                And(current_day_var == city_map[city1], next_day_var == city_map[city2])
                for city1 in direct_flights
                for city2 in direct_flights[city1]
            ]
        ))
    
    # Count the days per city
    counts = {city: 0 for city in cities}
    for city in cities:
        counts[city] = Sum([If(day_to_city[i] == city_map[city], 1, 0) for i in range(days)])
    
    # Add constraints for the required days per city
    s.add(counts['Hamburg'] == 2)
    s.add(counts['Zurich'] == 3)
    s.add(counts['Helsinki'] == 2)
    s.add(counts['Bucharest'] == 2)
    s.add(counts['Split'] == 7)
    
    # Wedding in Zurich between day 1 and day 3 (1-based)
    s.add(Or(day_to_city[0] == city_map['Zurich'], day_to_city[1] == city_map['Zurich'], day_to_city[2] == city_map['Zurich']))
    
    # Conference in Split on day 4 and day 10 (1-based, so index 3 and 9)
    s.add(day_to_city[3] == city_map['Split'])
    s.add(day_to_city[9] == city_map['Split'])
    
    # Check if the problem is satisfiable
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for i in range(days):
            city_idx = model.evaluate(day_to_city[i]).as_long()
            city = city_inv_map[city_idx]
            itinerary.append({"day": i + 1, "place": city})
        
        # Verify transitions are via direct flights
        for i in range(days - 1):
            current_city = itinerary[i]['place']
            next_city = itinerary[i + 1]['place']
            if current_city != next_city:
                assert next_city in direct_flights[current_city], f"No direct flight from {current_city} to {next_city}"
        
        # Verify day counts
        day_counts = {city: 0 for city in cities}
        for entry in itinerary:
            day_counts[entry['place']] += 1
        assert day_counts['Hamburg'] == 2
        assert day_counts['Zurich'] == 3
        assert day_counts['Helsinki'] == 2
        assert day_counts['Bucharest'] == 2
        assert day_counts['Split'] == 7
        
        # Verify wedding and conference days
        zurich_days = [entry['day'] for entry in itinerary if entry['place'] == 'Zurich']
        assert any(1 <= day <= 3 for day in zurich_days), "Wedding in Zurich not between day 1-3"
        split_days = [entry['day'] for entry in itinerary if entry['place'] == 'Split']
        assert 4 in split_days and 10 in split_days, "Conference days in Split not met"
        
        return {"itinerary": itinerary}
    else:
        return {"error": "No valid itinerary found"}

# Solve and print the itinerary
result = solve_itinerary()
print(result)