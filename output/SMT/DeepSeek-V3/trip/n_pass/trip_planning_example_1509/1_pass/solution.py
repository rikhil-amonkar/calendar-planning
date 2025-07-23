import json
from z3 import *

def solve_scheduling_problem():
    # Cities and their codes
    cities = {
        'Paris': 0,
        'Warsaw': 1,
        'Krakow': 2,
        'Tallinn': 3,
        'Riga': 4,
        'Copenhagen': 5,
        'Helsinki': 6,
        'Oslo': 7,
        'Santorini': 8,
        'Lyon': 9
    }
    
    # Reverse mapping for city names
    city_names = {v: k for k, v in cities.items()}
    
    # Direct flights (undirected)
    direct_flights = [
        (0, 1),  # Paris - Warsaw
        (0, 4),  # Paris - Riga
        (0, 3),  # Paris - Tallinn
        (0, 5),  # Paris - Copenhagen
        (0, 6),  # Paris - Helsinki
        (0, 7),  # Paris - Oslo
        (0, 2),  # Paris - Krakow
        (0, 9),  # Paris - Lyon
        (1, 4),  # Warsaw - Riga
        (1, 3),  # Warsaw - Tallinn
        (1, 5),  # Warsaw - Copenhagen
        (1, 6),  # Warsaw - Helsinki
        (1, 7),  # Warsaw - Oslo
        (1, 2),  # Warsaw - Krakow
        (2, 5),  # Krakow - Copenhagen
        (2, 6),  # Krakow - Helsinki
        (2, 7),  # Krakow - Oslo
        (3, 4),  # Tallinn - Riga
        (3, 5),  # Tallinn - Copenhagen
        (3, 6),  # Tallinn - Helsinki
        (3, 7),  # Tallinn - Oslo
        (4, 5),  # Riga - Copenhagen
        (4, 6),  # Riga - Helsinki
        (4, 7),  # Riga - Oslo
        (5, 6),  # Copenhagen - Helsinki
        (5, 7),  # Copenhagen - Oslo
        (5, 8),  # Copenhagen - Santorini
        (6, 7),  # Helsinki - Oslo
        (7, 8),  # Oslo - Santorini
        (7, 9),  # Oslo - Lyon
        (9, 0),  # Lyon - Paris
    ]
    
    # Create a set of directed flights (both directions)
    directed_flights = set()
    for a, b in direct_flights:
        directed_flights.add((a, b))
        directed_flights.add((b, a))
    
    # Total days
    total_days = 25
    
    # Create Z3 variables for each day
    day_vars = [Int(f'day_{i}') for i in range(1, total_days + 1)]
    
    # Solver
    s = Solver()
    
    # Each day must be a valid city
    for day in day_vars:
        s.add(day >= 0, day <= 9)
    
    # Duration constraints
    # Paris: 5 days
    s.add(Sum([If(day == cities['Paris'], 1, 0) for day in day_vars]) == 5)
    # Warsaw: 2 days
    s.add(Sum([If(day == cities['Warsaw'], 1, 0) for day in day_vars]) == 2)
    # Krakow: 2 days
    s.add(Sum([If(day == cities['Krakow'], 1, 0) for day in day_vars]) == 2)
    # Tallinn: 2 days
    s.add(Sum([If(day == cities['Tallinn'], 1, 0) for day in day_vars]) == 2)
    # Riga: 2 days
    s.add(Sum([If(day == cities['Riga'], 1, 0) for day in day_vars]) == 2)
    # Copenhagen: 5 days
    s.add(Sum([If(day == cities['Copenhagen'], 1, 0) for day in day_vars]) == 5)
    # Helsinki: 5 days
    s.add(Sum([If(day == cities['Helsinki'], 1, 0) for day in day_vars]) == 5)
    # Oslo: 5 days
    s.add(Sum([If(day == cities['Oslo'], 1, 0) for day in day_vars]) == 5)
    # Santorini: 2 days
    s.add(Sum([If(day == cities['Santorini'], 1, 0) for day in day_vars]) == 2)
    # Lyon: 4 days
    s.add(Sum([If(day == cities['Lyon'], 1, 0) for day in day_vars]) == 4)
    
    # Event constraints
    # Paris friends between day 4 and 8 (inclusive)
    s.add(Or([day_vars[i] == cities['Paris'] for i in range(3, 8)]))  # Days 4-8 (0-based: 3-7)
    # Krakow workshop between day 17 and 18 (inclusive)
    s.add(Or([day_vars[i] == cities['Krakow'] for i in range(16, 18)]))  # Days 17-18 (0-based: 16-17)
    # Riga wedding between day 23 and 24 (inclusive)
    s.add(Or([day_vars[i] == cities['Riga'] for i in range(22, 24)]))  # Days 23-24 (0-based: 22-23)
    # Helsinki friend between day 18 and 22 (inclusive)
    s.add(Or([day_vars[i] == cities['Helsinki'] for i in range(17, 22)]))  # Days 18-22 (0-based: 17-21)
    # Santorini relatives between day 12 and 13 (inclusive)
    s.add(Or([day_vars[i] == cities['Santorini'] for i in range(11, 13)]))  # Days 12-13 (0-based: 11-12)
    
    # Flight constraints: consecutive days must be either same city or have a direct flight
    for i in range(total_days - 1):
        current = day_vars[i]
        next_day = day_vars[i + 1]
        s.add(Or(current == next_day, Or([And(current == a, next_day == b) for (a, b) in directed_flights])))
    
    # Solve
    if s.check() == sat:
        m = s.model()
        itinerary = []
        for i in range(total_days):
            day = i + 1
            city_code = m.evaluate(day_vars[i]).as_long()
            city = city_names[city_code]
            itinerary.append({'day': day, 'place': city})
        
        # Verify the solution meets all constraints
        # (This is a sanity check; Z3 should ensure correctness)
        city_days = {city: 0 for city in cities}
        for entry in itinerary:
            city_days[entry['place']] += 1
        
        assert city_days['Paris'] == 5
        assert city_days['Warsaw'] == 2
        assert city_days['Krakow'] == 2
        assert city_days['Tallinn'] == 2
        assert city_days['Riga'] == 2
        assert city_days['Copenhagen'] == 5
        assert city_days['Helsinki'] == 5
        assert city_days['Oslo'] == 5
        assert city_days['Santorini'] == 2
        assert city_days['Lyon'] == 4
        
        # Check event constraints
        paris_days = [entry['day'] for entry in itinerary if entry['place'] == 'Paris']
        assert any(4 <= day <= 8 for day in paris_days)
        
        krakow_days = [entry['day'] for entry in itinerary if entry['place'] == 'Krakow']
        assert any(17 <= day <= 18 for day in krakow_days)
        
        riga_days = [entry['day'] for entry in itinerary if entry['place'] == 'Riga']
        assert any(23 <= day <= 24 for day in riga_days)
        
        helsinki_days = [entry['day'] for entry in itinerary if entry['place'] == 'Helsinki']
        assert any(18 <= day <= 22 for day in helsinki_days)
        
        santorini_days = [entry['day'] for entry in itinerary if entry['place'] == 'Santorini']
        assert any(12 <= day <= 13 for day in santorini_days)
        
        # Check flight constraints
        for i in range(len(itinerary) - 1):
            current = itinerary[i]['place']
            next_place = itinerary[i + 1]['place']
            if current != next_place:
                assert (cities[current], cities[next_place]) in directed_flights or (cities[next_place], cities[current]) in directed_flights
        
        return {'itinerary': itinerary}
    else:
        return {'error': 'No solution found'}

# Solve and print the result
result = solve_scheduling_problem()
print(json.dumps(result, indent=2))