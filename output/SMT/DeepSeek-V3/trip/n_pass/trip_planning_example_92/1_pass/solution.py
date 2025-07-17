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
        # Valid transitions:
        # Dublin <-> Riga
        # Riga -> Vilnius
        s.add(Or(
            current == next_c,  # stay in the same city
            And(current == Dublin, next_c == Riga),
            And(current == Riga, next_c == Dublin),
            And(current == Riga, next_c == Vilnius)
        ))
    
    # Count the days in each city
    count_Dublin = Sum([If(city[i] == Dublin, 1, 0) for i in range(days)])
    count_Riga = Sum([If(city[i] == Riga, 1, 0) for i in range(days)])
    count_Vilnius = Sum([If(city[i] == Vilnius, 1, 0) for i in range(days)])
    
    s.add(count_Dublin == 2)
    s.add(count_Riga == 5)
    s.add(count_Vilnius == 7)
    
    # Check if the model is satisfiable
    if s.check() == sat:
        m = s.model()
        itinerary = []
        for i in range(days):
            city_val = m.evaluate(city[i]).as_long()
            itinerary.append({'day': i + 1, 'place': city_names[city_val]})
        
        # Verify transitions are valid
        valid = True
        for i in range(days - 1):
            current = m.evaluate(city[i]).as_long()
            next_c = m.evaluate(city[i + 1]).as_long()
            if current != next_c:
                if not ((current == Dublin and next_c == Riga) or 
                        (current == Riga and next_c == Dublin) or 
                        (current == Riga and next_c == Vilnius)):
                    valid = False
                    break
        if not valid:
            print("Invalid transitions found.")
            return None
        
        # Verify day counts
        counts = {Dublin: 0, Riga: 0, Vilnius: 0}
        for i in range(days):
            c = m.evaluate(city[i]).as_long()
            counts[c] += 1
        if counts[Dublin] != 2 or counts[Riga] != 5 or counts[Vilnius] != 7:
            print("Day counts do not match.")
            return None
        
        return {'itinerary': itinerary}
    else:
        print("No solution found.")
        return None

# Execute the solver
result = solve_itinerary()
if result:
    import json
    print(json.dumps(result, indent=2))