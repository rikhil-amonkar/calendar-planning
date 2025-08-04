import json
from z3 import *

def solve_itinerary():
    # Cities and their required days
    cities = {
        'Oslo': 2,
        'Helsinki': 2,
        'Edinburgh': 3,
        'Riga': 2,
        'Tallinn': 5,
        'Budapest': 5,
        'Vilnius': 5,
        'Porto': 5,
        'Geneva': 4
    }
    
    # Direct flights (bidirectional)
    direct_flights = {
        'Porto': ['Oslo', 'Edinburgh', 'Geneva'],
        'Edinburgh': ['Porto', 'Budapest', 'Geneva', 'Oslo', 'Helsinki', 'Riga'],
        'Riga': ['Tallinn', 'Oslo', 'Helsinki', 'Vilnius'],
        'Tallinn': ['Riga', 'Vilnius', 'Helsinki', 'Oslo'],
        'Vilnius': ['Helsinki', 'Tallinn', 'Oslo', 'Riga'],
        'Helsinki': ['Vilnius', 'Tallinn', 'Edinburgh', 'Riga', 'Budapest', 'Oslo', 'Geneva'],
        'Budapest': ['Edinburgh', 'Geneva', 'Helsinki', 'Oslo'],
        'Geneva': ['Edinburgh', 'Porto', 'Budapest', 'Oslo', 'Helsinki'],
        'Oslo': ['Porto', 'Edinburgh', 'Riga', 'Geneva', 'Vilnius', 'Tallinn', 'Helsinki', 'Budapest']
    }
    
    # Create Z3 solver
    s = Solver()
    
    # Days are 1..25
    days = 25
    Day = IntSort()
    
    # Create a list of city variables for each day
    itinerary = [Const(f"day_{i}", Day) for i in range(1, days + 1)]
    
    # Assign each city a unique integer
    city_ids = {city: i for i, city in enumerate(cities.keys(), 1)}
    id_to_city = {i: city for city, i in city_ids.items()}
    
    # Constraint: Each day's assignment is one of the city IDs
    for day_var in itinerary:
        s.add(Or([day_var == city_ids[city] for city in cities]))
    
    # Constraint: Total days per city must match requirements
    for city in cities:
        total_days = Sum([If(day_var == city_ids[city], 1, 0) for day_var in itinerary])
        s.add(total_days == cities[city])
    
    # Constraint: Transitions between cities must have a direct flight
    for i in range(days - 1):
        current_city = itinerary[i]
        next_city = itinerary[i + 1]
        # Allow staying in the same city or moving to a directly connected city
        s.add(Or(
            current_city == next_city,
            *[And(current_city == city_ids[city], next_city == city_ids[neighbor])
              for city in direct_flights for neighbor in direct_flights[city]
            ]))
    
    # Special constraints:
    # Wedding in Tallinn between day 4 and 8 (inclusive)
    s.add(Or([itinerary[i] == city_ids['Tallinn'] for i in range(3, 8)]))  # days 4-8 (0-based 3-7)
    
    # Meet friend in Oslo between day 24 and 25 (so Oslo must be on day 24 or 25)
    s.add(Or(itinerary[23] == city_ids['Oslo'], itinerary[24] == city_ids['Oslo']))  # days 24-25 (0-based 23-24)
    
    # Check if the solver can find a solution
    if s.check() == sat:
        model = s.model()
        # Decode the itinerary
        decoded_itinerary = []
        for i in range(days):
            city_id = model.evaluate(itinerary[i]).as_long()
            city = id_to_city[city_id]
            decoded_itinerary.append({"day": i + 1, "place": city})
        
        # Prepare the output
        output = {"itinerary": decoded_itinerary}
        return output
    else:
        return {"error": "No valid itinerary found"}

# Solve and print the itinerary
itinerary = solve_itinerary()
print(json.dumps(itinerary, indent=2))