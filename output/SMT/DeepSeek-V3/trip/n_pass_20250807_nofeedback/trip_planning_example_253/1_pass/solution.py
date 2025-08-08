from z3 import *
import json

def solve_itinerary():
    # Cities
    cities = ['Amsterdam', 'Vienna', 'Santorini', 'Lyon']
    city_to_idx = {city: idx for idx, city in enumerate(cities)}
    
    # Direct flights: adjacency matrix
    direct_flights = [
        [False, True, True, True],   # Amsterdam
        [True, False, True, True],    # Vienna
        [True, True, False, False],   # Santorini
        [True, True, False, False]    # Lyon
    ]
    
    # Create solver
    s = Solver()
    
    # Variables: day[i] is the city index for day i+1 (days 1-14)
    days = [Int(f'day_{i}') for i in range(14)]
    
    # Each day must be 0, 1, 2, or 3 (city indices)
    for day in days:
        s.add(day >= 0, day <= 3)
    
    # Total days per city
    amsterdam_days = sum([If(days[i] == city_to_idx['Amsterdam'], 1, 0) for i in range(14)])
    vienna_days = sum([If(days[i] == city_to_idx['Vienna'], 1, 0) for i in range(14)])
    santorini_days = sum([If(days[i] == city_to_idx['Santorini'], 1, 0) for i in range(14)])
    lyon_days = sum([If(days[i] == city_to_idx['Lyon'], 1, 0) for i in range(14)])
    
    s.add(amsterdam_days == 3)
    s.add(vienna_days == 7)
    s.add(santorini_days == 4)
    s.add(lyon_days == 3)
    
    # Workshop in Amsterdam between day 9 and 11 (inclusive, 1-based)
    workshop_days = [If(days[i] == city_to_idx['Amsterdam'], 1, 0) for i in range(8, 11)]  # days 9-11 are indices 8-10 (0-based)
    s.add(Sum(workshop_days) >= 1)
    
    # Wedding in Lyon between day 7 and 9 (inclusive, 1-based)
    wedding_days = [If(days[i] == city_to_idx['Lyon'], 1, 0) for i in range(6, 9)]  # days 7-9 are indices 6-8 (0-based)
    s.add(Sum(wedding_days) >= 1)
    
    # Flight transitions: consecutive days must be the same city or have a direct flight
    for i in range(13):
        current_city = days[i]
        next_city = days[i+1]
        # Either same city or direct flight exists
        s.add(Or(
            current_city == next_city,
            And(current_city != next_city, 
                direct_flights[current_city][next_city])
        ))
    
    # Check for solution
    if s.check() == sat:
        m = s.model()
        itinerary = []
        for i in range(14):
            city_idx = m.evaluate(days[i]).as_long()
            itinerary.append({"day": i+1, "place": cities[city_idx]})
        
        # Verify the counts
        counts = {city: 0 for city in cities}
        for entry in itinerary:
            counts[entry["place"]] += 1
        
        # Prepare the output
        output = {"itinerary": itinerary}
        return output
    else:
        return {"error": "No valid itinerary found"}

# Generate and print the itinerary
itinerary = solve_itinerary()
print(json.dumps(itinerary, indent=2))