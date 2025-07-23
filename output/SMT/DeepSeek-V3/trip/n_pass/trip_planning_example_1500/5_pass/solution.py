from z3 import *

def solve_itinerary():
    # Cities to visit and their required days
    cities = {
        'Zurich': 2,
        'Bucharest': 2,
        'Hamburg': 5,
        'Barcelona': 4,
        'Reykjavik': 5,
        'Stuttgart': 5,
        'Stockholm': 2,
        'Tallinn': 4,
        'Milan': 5,
        'London': 3
    }
    
    # Corrected and verified direct flights
    direct_flights = {
        ('London', 'Hamburg'), ('London', 'Reykjavik'), ('Milan', 'Barcelona'),
        ('Reykjavik', 'Barcelona'), ('Reykjavik', 'Stuttgart'), ('Stockholm', 'Reykjavik'),
        ('London', 'Stuttgart'), ('Milan', 'Zurich'), ('London', 'Barcelona'),
        ('Stockholm', 'Hamburg'), ('Zurich', 'Barcelona'), ('Stockholm', 'Stuttgart'),
        ('Milan', 'Hamburg'), ('Stockholm', 'Tallinn'), ('Hamburg', 'Bucharest'),
        ('London', 'Bucharest'), ('Milan', 'Stockholm'), ('Stuttgart', 'Hamburg'),
        ('London', 'Zurich'), ('Milan', 'Reykjavik'), ('London', 'Stockholm'),
        ('Milan', 'Stuttgart'), ('Stockholm', 'Barcelona'), ('London', 'Milan'),
        ('Zurich', 'Hamburg'), ('Bucharest', 'Barcelona'), ('Zurich', 'Stockholm'),
        ('Barcelona', 'Tallinn'), ('Zurich', 'Tallinn'), ('Hamburg', 'Barcelona'),
        ('Stuttgart', 'Barcelona'), ('Zurich', 'Reykjavik'), ('Zurich', 'Bucharest')
    }
    
    # Make flights bidirectional
    bidirectional_flights = set()
    for (a, b) in direct_flights:
        bidirectional_flights.add((a, b))
        bidirectional_flights.add((b, a))
    direct_flights = bidirectional_flights
    
    # Create Z3 solver
    s = Solver()
    
    # Create variables for each day (1-28)
    itinerary = [Int(f'day_{i}') for i in range(1, 29)]
    
    # Map cities to integers
    city_ids = {city: idx for idx, city in enumerate(cities.keys())}
    id_to_city = {idx: city for city, idx in city_ids.items()}
    
    # Each day must be assigned to a valid city
    for day in itinerary:
        s.add(Or([day == city_ids[city] for city in cities]))
    
    # Fixed constraints:
    # London days 1-3
    for d in [0, 1, 2]:
        s.add(itinerary[d] == city_ids['London'])
    
    # Zurich days 7-8
    s.add(itinerary[6] == city_ids['Zurich'])
    s.add(itinerary[7] == city_ids['Zurich'])
    
    # Reykjavik days 9-13
    for d in range(8, 13):
        s.add(itinerary[d] == city_ids['Reykjavik'])
    
    # Milan days 3-6 (since day 7 is Zurich)
    for d in range(2, 6):
        s.add(itinerary[d] == city_ids['Milan'])
    
    # Duration constraints for each city
    for city in cities:
        required_days = cities[city]
        sum_days = Sum([If(itinerary[d] == city_ids[city], 1, 0) for d in range(28)])
        s.add(sum_days == required_days)
    
    # Flight transitions between consecutive days
    for d in range(27):
        current = itinerary[d]
        next_day = itinerary[d + 1]
        # Either stay in same city or take direct flight
        s.add(Or(
            current == next_day,
            *[And(current == city_ids[a], next_day == city_ids[b]) 
              for (a, b) in direct_flights]
        ))
    
    # Try to find a solution
    if s.check() == sat:
        model = s.model()
        result = []
        for d in range(28):
            city_id = model.evaluate(itinerary[d]).as_long()
            result.append({"day": d+1, "place": id_to_city[city_id]})
        
        # Verification
        counts = {city: 0 for city in cities}
        for entry in result:
            counts[entry['place']] += 1
        for city in cities:
            assert counts[city] == cities[city], f"City {city} has incorrect days"
        
        for d in range(27):
            curr = result[d]['place']
            next_p = result[d+1]['place']
            if curr != next_p:
                assert (curr, next_p) in direct_flights, f"No flight {curr}->{next_p}"
        
        return {"itinerary": result}
    else:
        return {"error": "No valid itinerary found"}

# Run the solver
solution = solve_itinerary()
import json
print(json.dumps(solution, indent=2))