from z3 import *

def solve_itinerary():
    # Cities: Dublin (0), Riga (1), Vilnius (2)
    Dublin, Riga, Vilnius = 0, 1, 2
    city_names = {Dublin: 'Dublin', Riga: 'Riga', Vilnius: 'Vilnius'}
    
    s = Solver()
    
    # 12 days, each day is assigned a city
    days = 12
    city = [Int(f'city_{i}') for i in range(days)]
    
    # Each day must be one of the three cities
    for i in range(days):
        s.add(Or(city[i] == Dublin, city[i] == Riga, city[i] == Vilnius))
    
    # Flight constraints: transitions between cities must be valid direct flights
    for i in range(days - 1):
        current = city[i]
        next_c = city[i + 1]
        s.add(Or(
            current == next_c,  # stay in same city
            And(current == Dublin, next_c == Riga),  # Dublin -> Riga
            And(current == Riga, next_c == Dublin),  # Riga -> Dublin
            And(current == Riga, next_c == Vilnius)  # Riga -> Vilnius
        ))
    
    # Count days in each city
    count_Dublin = Sum([If(city[i] == Dublin, 1, 0) for i in range(days)])
    count_Riga = Sum([If(city[i] == Riga, 1, 0) for i in range(days)])
    count_Vilnius = Sum([If(city[i] == Vilnius, 1, 0) for i in range(days)])
    
    s.add(count_Dublin == 2)
    s.add(count_Riga == 5)
    s.add(count_Vilnius == 7)
    
    # Additional constraints to help the solver
    # Must start in Dublin or Riga (cities with outgoing flights)
    s.add(Or(city[0] == Dublin, city[0] == Riga))
    
    # Must visit all three cities
    s.add(Or([city[i] == Dublin for i in range(days)]))
    s.add(Or([city[i] == Riga for i in range(days)]))
    s.add(Or([city[i] == Vilnius for i in range(days)]))
    
    # Check if solution exists
    if s.check() == sat:
        m = s.model()
        itinerary = []
        for i in range(days):
            city_val = m.evaluate(city[i]).as_long()
            itinerary.append({'day': i + 1, 'place': city_names[city_val]})
        
        # Verify solution
        counts = {Dublin: 0, Riga: 0, Vilnius: 0}
        for i in range(days):
            c = m.evaluate(city[i]).as_long()
            counts[c] += 1
        
        if (counts[Dublin] == 2 and counts[Riga] == 5 and counts[Vilnius] == 7 and
            all(city_names[m.evaluate(city[i]).as_long()] in ['Dublin', 'Riga', 'Vilnius'] for i in range(days))):
            return {'itinerary': itinerary}
        else:
            print("Invalid solution found")
            return None
    else:
        print("No solution exists with given constraints")
        return None

# Execute and print result
result = solve_itinerary()
if result:
    import json
    print(json.dumps(result, indent=2))