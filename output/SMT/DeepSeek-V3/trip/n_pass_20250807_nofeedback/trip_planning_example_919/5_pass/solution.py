from z3 import *

def solve_itinerary():
    # Cities
    cities = ['Vienna', 'Milan', 'Rome', 'Riga', 'Lisbon', 'Vilnius', 'Oslo']
    city_to_idx = {city: idx for idx, city in enumerate(cities)}
    
    # Direct flights: adjacency list
    direct_flights = {
        'Vienna': ['Milan', 'Vilnius', 'Lisbon', 'Riga', 'Rome', 'Oslo'],
        'Milan': ['Vienna', 'Riga', 'Oslo', 'Lisbon', 'Vilnius'],
        'Rome': ['Oslo', 'Riga', 'Lisbon', 'Vienna'],
        'Riga': ['Oslo', 'Milan', 'Vilnius', 'Lisbon', 'Vienna', 'Rome'],
        'Lisbon': ['Vienna', 'Oslo', 'Rome', 'Riga', 'Milan'],
        'Vilnius': ['Vienna', 'Oslo', 'Riga', 'Milan'],
        'Oslo': ['Riga', 'Rome', 'Lisbon', 'Milan', 'Vienna', 'Vilnius']
    }
    
    # Create a Z3 solver instance
    s = Solver()
    
    # Variables: day_1 to day_15, each can be one of the cities
    days = [Int(f'day_{i}') for i in range(1, 16)]
    
    # Each day variable must be between 0 and 6 (index of cities)
    for day in days:
        s.add(day >= 0, day < len(cities))
    
    # Fixed constraints:
    # Day 1 and day 4 in Vienna (city index 0)
    s.add(days[0] == city_to_idx['Vienna'])
    s.add(days[3] == city_to_idx['Vienna'])
    
    # Relatives in Lisbon between day 11 and 13 (indices 10, 11, 12)
    s.add(Or([days[i] == city_to_idx['Lisbon'] for i in range(10, 13)]))
    
    # Friend in Oslo between day 13 and 15 (indices 12, 13, 14)
    s.add(Or([days[i] == city_to_idx['Oslo'] for i in range(12, 15)]))
    
    # Flight constraints: consecutive days must be either same city or connected by direct flight
    for i in range(14):  # days 1..15, compare day i and i+1 (0-based)
        current_day = days[i]
        next_day = days[i+1]
        # Either stay in the same city or move to a directly connected city
        same_city = (current_day == next_day)
        possible_transitions = []
        for city in direct_flights:
            for neighbor in direct_flights[city]:
                possible_transitions.append(And(current_day == city_to_idx[city], next_day == city_to_idx[neighbor]))
        s.add(Or(same_city, *possible_transitions))
    
    # Duration constraints:
    # Vienna: 4 days (including day 1 and 4)
    vienna_days = Sum([If(days[i] == city_to_idx['Vienna'], 1, 0) for i in range(15)])
    s.add(vienna_days == 4)
    
    # Milan: 2 days
    milan_days = Sum([If(days[i] == city_to_idx['Milan'], 1, 0) for i in range(15)])
    s.add(milan_days == 2)
    
    # Rome: 3 days
    rome_days = Sum([If(days[i] == city_to_idx['Rome'], 1, 0) for i in range(15)])
    s.add(rome_days == 3)
    
    # Riga: 2 days
    riga_days = Sum([If(days[i] == city_to_idx['Riga'], 1, 0) for i in range(15)])
    s.add(riga_days == 2)
    
    # Lisbon: 3 days
    lisbon_days = Sum([If(days[i] == city_to_idx['Lisbon'], 1, 0) for i in range(15)])
    s.add(lisbon_days == 3)
    
    # Vilnius: 4 days
    vilnius_days = Sum([If(days[i] == city_to_idx['Vilnius'], 1, 0) for i in range(15)])
    s.add(vilnius_days == 4)
    
    # Oslo: 3 days
    oslo_days = Sum([If(days[i] == city_to_idx['Oslo'], 1, 0) for i in range(15)])
    s.add(oslo_days == 3)
    
    # Check if the problem is satisfiable
    if s.check() == sat:
        m = s.model()
        itinerary = []
        for i in range(15):
            day_num = i + 1
            city_idx = m.evaluate(days[i]).as_long()
            city = cities[city_idx]
            itinerary.append({"day": day_num, "place": city})
        
        # Create the JSON output
        output = {
            "itinerary": itinerary
        }
        return output
    else:
        return {"error": "No valid itinerary found"}

# Generate the solution
solution = solve_itinerary()
import json
print(json.dumps(solution, indent=2))