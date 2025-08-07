from z3 import *
import json

def solve_itinerary():
    # Cities mapping
    cities = {
        'London': 0,
        'Copenhagen': 1,
        'Tallinn': 2,
        'Oslo': 3,
        'Nice': 4,
        'Mykonos': 5
    }
    inv_cities = {v: k for k, v in cities.items()}
    
    # Direct flights: adjacency list
    direct_flights = {
        0: [1, 3, 4, 5],  # London
        1: [0, 2, 3, 4],   # Copenhagen
        2: [1, 3],         # Tallinn
        3: [0, 2, 1, 4],    # Oslo
        4: [0, 3, 5, 1],    # Nice
        5: [0, 4]           # Mykonos
    }
    
    # Create Z3 variables for each day's city
    days = 16
    day_city = [Int(f'day_{i+1}_city') for i in range(days)]
    
    s = Solver()
    
    # Each day's city must be one of the cities (0-5)
    for day in day_city:
        s.add(Or([day == c for c in cities.values()]))
    
    # Flight constraints: consecutive days must be the same city or connected by a direct flight
    for i in range(days - 1):
        current_city = day_city[i]
        next_city = day_city[i + 1]
        # Create a condition for each possible current city
        constraints = []
        for city in cities.values():
            allowed_next = direct_flights[city]
            constraints.append(And(current_city == city, Or([next_city == c for c in allowed_next])))
        s.add(Or(current_city == next_city, Or(constraints)))
    
    # Duration constraints
    # Mykonos: 4 days
    mykonos_days = Sum([If(day == cities['Mykonos'], 1, 0) for day in day_city])
    s.add(mykonos_days == 4)
    
    # Nice: 3 days total, but must be present on days 14,15,16 (since conference is days 14-16)
    nice_days = Sum([If(day == cities['Nice'], 1, 0) for day in day_city])
    s.add(nice_days == 3)
    s.add(day_city[13] == cities['Nice'])  # day 14 is index 13 (0-based)
    s.add(day_city[14] == cities['Nice'])  # day 15
    s.add(day_city[15] == cities['Nice'])  # day 16
    
    # London: 2 days
    london_days = Sum([If(day == cities['London'], 1, 0) for day in day_city])
    s.add(london_days == 2)
    
    # Copenhagen: 3 days
    copenhagen_days = Sum([If(day == cities['Copenhagen'], 1, 0) for day in day_city])
    s.add(copenhagen_days == 3)
    
    # Oslo: 5 days, and must be visited between day 10 and 14 (i.e., at least one day in Oslo in days 10-14)
    oslo_days = Sum([If(day == cities['Oslo'], 1, 0) for day in day_city])
    s.add(oslo_days == 5)
    # At least one day in Oslo between day 10 and 14 (indices 9 to 13 inclusive)
    s.add(Or([day_city[i] == cities['Oslo'] for i in range(9, 14)]))
    
    # Tallinn: 4 days
    tallinn_days = Sum([If(day == cities['Tallinn'], 1, 0) for day in day_city])
    s.add(tallinn_days == 4)
    
    # Solve the problem
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for i in range(days):
            city_code = model.evaluate(day_city[i]).as_long()
            itinerary.append({
                'day': i + 1,
                'place': inv_cities[city_code]
            })
        
        # Prepare the output
        output = {
            'itinerary': itinerary
        }
        return output
    else:
        return {"error": "No valid itinerary found"}

# Generate and print the solution
solution = solve_itinerary()
print(json.dumps(solution, indent=2))