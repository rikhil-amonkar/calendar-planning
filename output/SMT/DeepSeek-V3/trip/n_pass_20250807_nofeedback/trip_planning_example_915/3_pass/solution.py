from z3 import *

def solve_scheduling():
    # Cities
    cities = ['Bucharest', 'Venice', 'Prague', 'Frankfurt', 'Zurich', 'Florence', 'Tallinn']
    city_to_idx = {city: idx for idx, city in enumerate(cities)}
    
    # Direct flights: adjacency list
    direct_flights = {
        'Prague': ['Tallinn', 'Zurich', 'Florence', 'Bucharest', 'Frankfurt'],
        'Tallinn': ['Prague', 'Frankfurt', 'Zurich'],
        'Zurich': ['Prague', 'Florence', 'Bucharest', 'Frankfurt', 'Venice'],
        'Florence': ['Prague', 'Frankfurt', 'Zurich'],
        'Frankfurt': ['Bucharest', 'Venice', 'Tallinn', 'Zurich', 'Prague', 'Florence'],
        'Bucharest': ['Frankfurt', 'Prague', 'Zurich'],
        'Venice': ['Frankfurt', 'Zurich']
    }
    
    # Create Z3 variables: day 1 to 26, each is an integer representing city index
    days = [Int(f"day_{i}") for i in range(1, 27)]
    
    s = Solver()
    
    # Each day must be a valid city index (0 to 6)
    for day in days:
        s.add(And(day >= 0, day <= 6))
    
    # Transition constraints: consecutive days must be either same city or connected by direct flight
    for i in range(25):
        current_day = days[i]
        next_day = days[i+1]
        # Either same city or flight exists
        same_city = (current_day == next_day)
        flight_possible = Or([And(current_day == city_to_idx[a], next_day == city_to_idx[b]) 
                            for a in direct_flights for b in direct_flights[a]])
        s.add(Or(same_city, flight_possible))
    
    # Bucharest: 3 days total
    s.add(Sum([If(days[i] == city_to_idx['Bucharest'], 1, 0) for i in range(26)]) == 3)
    
    # Venice: 5 days total, wedding between day 22-26 (must be in Venice during at least one of these days)
    s.add(Sum([If(days[i] == city_to_idx['Venice'], 1, 0) for i in range(26)]) == 5)
    # At least one day between 22-26 (0-based: days 21-25) must be Venice
    s.add(Or([days[i] == city_to_idx['Venice'] for i in range(21, 26)]))
    
    # Prague: 4 days
    s.add(Sum([If(days[i] == city_to_idx['Prague'], 1, 0) for i in range(26)]) == 4)
    
    # Frankfurt: 5 days, annual show day 12-16 (0-based: days 11-15)
    s.add(Sum([If(days[i] == city_to_idx['Frankfurt'], 1, 0) for i in range(26)]) == 5)
    # All days 12-16 must be Frankfurt (days 11-15 in 0-based)
    for i in range(11, 16):
        s.add(days[i] == city_to_idx['Frankfurt'])
    
    # Zurich: 5 days
    s.add(Sum([If(days[i] == city_to_idx['Zurich'], 1, 0) for i in range(26)]) == 5)
    
    # Florence: 5 days
    s.add(Sum([If(days[i] == city_to_idx['Florence'], 1, 0) for i in range(26)]) == 5)
    
    # Tallinn: 5 days, friends between day 8-12 (0-based: days 7-11)
    s.add(Sum([If(days[i] == city_to_idx['Tallinn'], 1, 0) for i in range(26)]) == 5)
    # At least one day between 8-12 must be Tallinn (days 7-11)
    s.add(Or([days[i] == city_to_idx['Tallinn'] for i in range(7, 12)]))
    
    # Check if the problem is satisfiable
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for i in range(26):
            day_num = i + 1
            city_idx = model.evaluate(days[i]).as_long()
            city = cities[city_idx]
            itinerary.append({"day": day_num, "place": city})
        
        # Verify the solution meets all constraints
        # (Additional checks can be added here if needed)
        
        # Format the output as JSON
        import json
        output = {"itinerary": itinerary}
        print(json.dumps(output, indent=2))
    else:
        print("No valid itinerary found.")

solve_scheduling()