from z3 import *
import json

def solve_itinerary():
    # Cities and their required days
    cities = ['Berlin', 'Split', 'Bucharest', 'Riga', 'Lisbon', 'Tallinn', 'Lyon']
    required_days = {
        'Berlin': 5,
        'Split': 3,
        'Bucharest': 3,
        'Riga': 5,
        'Lisbon': 3,
        'Tallinn': 4,
        'Lyon': 5
    }
    
    # Direct flights as a set of tuples
    direct_flights = {
        ('Lisbon', 'Bucharest'),
        ('Berlin', 'Lisbon'),
        ('Bucharest', 'Riga'),
        ('Berlin', 'Riga'),
        ('Split', 'Lyon'),
        ('Lisbon', 'Riga'),
        ('Riga', 'Tallinn'),
        ('Berlin', 'Split'),
        ('Lyon', 'Lisbon'),
        ('Berlin', 'Tallinn'),
        ('Lyon', 'Bucharest')
    }
    # Ensure flights are bidirectional
    bidirectional_flights = set()
    for (a, b) in direct_flights:
        bidirectional_flights.add((a, b))
        bidirectional_flights.add((b, a))
    direct_flights = bidirectional_flights
    
    # Create a Z3 solver
    solver = Solver()
    
    # Variables: day_1 to day_22, each can be one of the cities
    days = [Int(f'day_{i}') for i in range(1, 23)]
    
    # Each day's variable must be between 0 and 6 (representing the cities)
    city_to_num = {city: idx for idx, city in enumerate(cities)}
    num_to_city = {idx: city for idx, city in enumerate(cities)}
    
    for day in days:
        solver.add(day >= 0, day < len(cities))
    
    # Fixed constraints:
    # Berlin from day 1 to 5
    for i in range(1, 6):
        solver.add(days[i-1] == city_to_num['Berlin'])
    
    # Bucharest between day 13 and 15 (3 days)
    # So, Bucharest must be visited on three consecutive days within day 13-15.
    # Possible sequences are 13-15, 12-14, or 14-16, but 13-15 is the most likely.
    # But the problem says between day 13 and 15, which could mean days 13, 14, and 15.
    solver.add(And(
        days[12] == city_to_num['Bucharest'],
        days[13] == city_to_num['Bucharest'],
        days[14] == city_to_num['Bucharest']
    ))
    
    # Lyon between day 7 and 11 (5 days)
    for i in range(7, 12):
        solver.add(days[i-1] == city_to_num['Lyon'])
    
    # Flight constraints: consecutive days must be same city or have a direct flight
    for i in range(1, 22):
        current_day = days[i-1]
        next_day = days[i]
        solver.add(Or(
            current_day == next_day,
            And(current_day != next_day,
                Or(*[And(current_day == city_to_num[a], next_day == city_to_num[b]) for (a, b) in direct_flights])
        ))
    
    # Duration constraints: each city must be visited for the required number of days
    for city in cities:
        count = 0
        for day in days:
            count += If(day == city_to_num[city], 1, 0)
        solver.add(count == required_days[city])
    
    # Check if the solver can find a solution
    if solver.check() == sat:
        model = solver.model()
        itinerary = []
        for i in range(1, 23):
            city_num = model.evaluate(days[i-1]).as_long()
            city = num_to_city[city_num]
            itinerary.append({"day": i, "place": city})
        
        # Convert to the required JSON format
        result = {"itinerary": itinerary}
        return json.dumps(result, indent=2)
    else:
        return json.dumps({"error": "No valid itinerary found"}, indent=2)

# Run the solver and print the result
print(solve_itinerary())