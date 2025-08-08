from z3 import *

def solve_itinerary():
    # Cities
    cities = ['Mykonos', 'Nice', 'London', 'Copenhagen', 'Oslo', 'Tallinn']
    Mykonos, Nice, London, Copenhagen, Oslo, Tallinn = cities
    city_map = {city: idx for idx, city in enumerate(cities)}
    
    # Direct flights as adjacency list
    direct_flights = {
        Mykonos: [London, Nice],
        Nice: [Mykonos, London, Oslo, Copenhagen],
        London: [Mykonos, Nice, Copenhagen, Oslo],
        Copenhagen: [London, Tallinn, Nice, Oslo],
        Oslo: [Tallinn, Nice, London, Copenhagen],
        Tallinn: [Copenhagen, Oslo]
    }
    
    # Create solver
    s = Solver()
    
    # Variables: day[i] is the city visited on day i+1 (days are 1-based)
    days = [Int(f'day_{i}') for i in range(16)]
    for day in days:
        s.add(day >= 0, day < len(cities))
    
    # Helper function to get city name from index
    def city_name(idx):
        return cities[idx]
    
    # Constraints for each day's transitions (must be direct flight or same city)
    for i in range(15):
        current_day = days[i]
        next_day = days[i+1]
        # Either stay in the same city or move to a directly connected city
        s.add(Or(
            current_day == next_day,
            # Check if there's a direct flight between current city and next city
            Or([And(current_day == city_map[a], next_day == city_map[b]) 
                for a in direct_flights for b in direct_flights[a]])
        ))
    
    # Total days per city constraints
    total_days = {
        Mykonos: 4,
        Nice: 3,
        London: 2,
        Copenhagen: 3,
        Oslo: 5,
        Tallinn: 4
    }
    
    for city in cities:
        count = Sum([If(days[i] == city_map[city], 1, 0) for i in range(16)])
        s.add(count == total_days[city])
    
    # Conference in Nice on days 14-16 (1-based, so indices 13-15)
    s.add(days[13] == city_map[Nice])
    s.add(days[14] == city_map[Nice])
    s.add(days[15] == city_map[Nice])
    
    # Meet friend in Oslo between day 10 and 14 (days 10-14, indices 9-13)
    s.add(Or([days[i] == city_map[Oslo] for i in range(9, 14)]))
    
    # Solve the problem
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for i in range(16):
            city_idx = model.evaluate(days[i]).as_long()
            itinerary.append({"day": i+1, "place": cities[city_idx]})
        
        # Verify contiguous stays (not strictly necessary per problem statement)
        # But the constraints should ensure validity
        
        # Prepare the output
        output = {"itinerary": itinerary}
        return output
    else:
        return {"error": "No valid itinerary found"}

# Execute and print the result
result = solve_itinerary()
print(result)