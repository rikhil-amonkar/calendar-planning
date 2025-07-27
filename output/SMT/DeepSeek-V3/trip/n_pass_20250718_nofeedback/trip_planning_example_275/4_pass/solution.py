from z3 import *
import json

def solve_itinerary():
    # Cities
    cities = ['Split', 'Vilnius', 'Santorini', 'Madrid']
    city_to_int = {city: idx for idx, city in enumerate(cities)}
    
    # Direct flight connections (undirected)
    connections = {
        ('Vilnius', 'Split'),
        ('Split', 'Madrid'),
        ('Madrid', 'Santorini')
    }
    
    # Convert connections to indices for easier checking
    connection_indices = set()
    for a, b in connections:
        connection_indices.add((city_to_int[a], city_to_int[b]))
        connection_indices.add((city_to_int[b], city_to_int[a]))
    
    # Days: 1 to 14
    num_days = 14
    
    # Create Z3 variables for each day's city
    day_vars = [Int(f'day_{i}') for i in range(1, num_days + 1)]
    
    # Solver
    s = Solver()
    
    # Each day's variable must be one of the city indices (0 to 3)
    for day_var in day_vars:
        s.add(Or([day_var == idx for idx in range(len(cities))]))
    
    # Conference days 13 and 14 must be Santorini (index 2)
    s.add(day_vars[12] == city_to_int['Santorini'])  # day 13 is index 12 (0-based)
    s.add(day_vars[13] == city_to_int['Santorini'])  # day 14
    
    # Transition constraints: consecutive days must be the same city or connected by direct flight
    for i in range(num_days - 1):
        current_city = day_vars[i]
        next_city = day_vars[i + 1]
        s.add(Or(
            current_city == next_city,
            And(current_city != next_city, (current_city, next_city) in connection_indices)
        ))
    
    # Duration constraints
    split_days = sum([If(day_var == city_to_int['Split'], 1, 0) for day_var in day_vars])
    vilnius_days = sum([If(day_var == city_to_int['Vilnius'], 1, 0) for day_var in day_vars])
    santorini_days = sum([If(day_var == city_to_int['Santorini'], 1, 0) for day_var in day_vars])
    madrid_days = sum([If(day_var == city_to_int['Madrid'], 1, 0) for day_var in day_vars])
    
    s.add(split_days == 5)
    s.add(vilnius_days == 4)
    s.add(santorini_days == 2)  # days 13 and 14 are already forced
    s.add(madrid_days == 6)
    
    # Solve
    if s.check() == sat:
        m = s.model()
        itinerary = []
        int_to_city = {idx: city for city, idx in city_to_int.items()}
        for day in range(1, num_days + 1):
            day_var = day_vars[day - 1]
            city_idx = m.evaluate(day_var).as_long()
            city = int_to_city[city_idx]
            itinerary.append({'day': day, 'place': city})
        
        # Verify the solution meets all constraints
        # (split, vilnius, santorini, madrid days)
        split_count = sum(1 for entry in itinerary if entry['place'] == 'Split')
        vilnius_count = sum(1 for entry in itinerary if entry['place'] == 'Vilnius')
        santorini_count = sum(1 for entry in itinerary if entry['place'] == 'Santorini')
        madrid_count = sum(1 for entry in itinerary if entry['place'] == 'Madrid')
        
        assert split_count == 5
        assert vilnius_count == 4
        assert santorini_count == 2
        assert madrid_count == 6
        
        # Verify conference days
        assert itinerary[12]['place'] == 'Santorini'  # day 13
        assert itinerary[13]['place'] == 'Santorini'  # day 14
        
        # Verify transitions are valid
        for i in range(len(itinerary) - 1):
            current = itinerary[i]['place']
            next_ = itinerary[i + 1]['place']
            if current != next_:
                assert (current, next_) in connections or (next_, current) in connections
        
        # Prepare the output
        output = {'itinerary': itinerary}
        return output
    else:
        return {"error": "No valid itinerary found"}

# Generate and print the itinerary
result = solve_itinerary()
print(json.dumps(result, indent=2))