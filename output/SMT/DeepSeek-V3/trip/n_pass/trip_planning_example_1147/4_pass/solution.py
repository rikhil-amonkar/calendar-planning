from z3 import *
import json

def solve_itinerary():
    # Cities
    cities = ['Brussels', 'Helsinki', 'Split', 'Dubrovnik', 'Istanbul', 'Milan', 'Vilnius', 'Frankfurt']
    city_vars = {city: [Bool(f'{city}_{day}') for day in range(1, 23)] for city in cities}
    
    # Corrected direct flights (undirected)
    direct_flights = {
        'Milan': ['Frankfurt', 'Split', 'Vilnius', 'Brussels', 'Helsinki', 'Istanbul'],
        'Split': ['Frankfurt', 'Milan', 'Helsinki', 'Vilnius'],
        'Brussels': ['Vilnius', 'Helsinki', 'Istanbul', 'Milan', 'Frankfurt'],
        'Helsinki': ['Brussels', 'Istanbul', 'Vilnius', 'Dubrovnik', 'Frankfurt', 'Split', 'Milan'],
        'Istanbul': ['Brussels', 'Helsinki', 'Dubrovnik', 'Milan', 'Frankfurt', 'Vilnius'],
        'Dubrovnik': ['Helsinki', 'Istanbul', 'Frankfurt'],
        'Frankfurt': ['Milan', 'Split', 'Brussels', 'Helsinki', 'Dubrovnik', 'Istanbul', 'Vilnius'],
        'Vilnius': ['Brussels', 'Milan', 'Helsinki', 'Split', 'Frankfurt', 'Istanbul']
    }
    
    s = Solver()
    
    # Each day, the traveler is in at least one city (could be two if it's a flight day)
    for day in range(1, 23):
        s.add(Or([city_vars[city][day-1] for city in cities]))
    
    # Flight day constraints: if a day is a flight day, then exactly two cities are true for that day
    # and they must be connected by a direct flight
    for day in range(1, 23):
        for city1 in cities:
            for city2 in cities:
                if city1 != city2:
                    s.add(Implies(And(city_vars[city1][day-1], city_vars[city2][day-1]),
                                (city2 in direct_flights[city1])))
    
    # No more than two cities per day (since flight day involves two cities)
    for day in range(1, 23):
        s.add(Sum([If(city_vars[city][day-1], 1, 0) for city in cities]) <= 2)
    
    # Total days per city
    city_days = {
        'Brussels': 3,
        'Helsinki': 3,
        'Split': 4,
        'Dubrovnik': 2,
        'Istanbul': 5,
        'Milan': 4,
        'Vilnius': 5,
        'Frankfurt': 3
    }
    for city in cities:
        s.add(Sum([If(city_vars[city][day-1], 1, 0) for day in range(1, 23)]) == city_days[city])
    
    # Fixed events
    # Istanbul: days 1-5 (must be there on these days)
    for day in range(1, 6):
        s.add(city_vars['Istanbul'][day-1])
    
    # Vilnius: workshop between day 18-22 (must be there at least one day in this range)
    s.add(Or([city_vars['Vilnius'][day-1] for day in range(18, 23)]))
    
    # Frankfurt: wedding between day 16-18 (must be there at least one day in this range)
    s.add(Or([city_vars['Frankfurt'][day-1] for day in range(16, 19)]))
    
    # Additional constraints to ensure proper sequencing
    # If in a city on day X and X+1, must be same city unless it's a flight day
    for day in range(1, 22):
        for city in cities:
            s.add(Implies(And(city_vars[city][day-1], city_vars[city][day]),
                        Or([city_vars[city][day] for city in cities])))
    
    # Solve the model
    if s.check() == sat:
        model = s.model()
        itinerary = []
        current_cities = []
        
        # Group consecutive days in same city
        day = 1
        while day <= 22:
            cities_today = [city for city in cities if is_true(model[city_vars[city][day-1]])]
            
            if len(cities_today) == 1:
                # Single city - find consecutive days
                city = cities_today[0]
                start_day = day
                while day <= 22 and is_true(model[city_vars[city][day-1]]):
                    day += 1
                itinerary.append({'day_range': f'Day {start_day}-{day-1}', 'place': city})
            else:
                # Flight day - handle separately
                itinerary.append({'day_range': f'Day {day}-{day}', 
                                 'place': f"{cities_today[0]}/{cities_today[1]}"})
                day += 1
        
        # Verify all constraints are met
        # Count days per city
        day_counts = {city: 0 for city in cities}
        for entry in itinerary:
            if '/' in entry['place']:
                # Flight day - count for both cities
                city1, city2 = entry['place'].split('/')
                day_counts[city1] += 1
                day_counts[city2] += 1
            else:
                # Regular stay
                start, end = map(int, entry['day_range'].split('-')[0].split(' ')[1].split('-'))
                day_counts[entry['place']] += (end - start + 1)
        
        # Check if all day counts match requirements
        for city, required in city_days.items():
            assert day_counts[city] == required, f"Day count mismatch for {city}"
        
        # Check fixed events
        istanbul_days = [entry for entry in itinerary if 'Istanbul' in entry['place']]
        assert all(1 <= int(day.split('-')[0]) <= 5 for entry in istanbul_days 
                  for day in [entry['day_range'].split(' ')[1]]), "Istanbul days 1-5 not satisfied"
        
        vilnius_days = [entry for entry in itinerary if 'Vilnius' in entry['place']]
        assert any(18 <= int(day.split('-')[0]) <= 22 for entry in vilnius_days 
                  for day in [entry['day_range'].split(' ')[1]]), "Vilnius days 18-22 not satisfied"
        
        frankfurt_days = [entry for entry in itinerary if 'Frankfurt' in entry['place']]
        assert any(16 <= int(day.split('-')[0]) <= 18 for entry in frankfurt_days 
                  for day in [entry['day_range'].split(' ')[1]]), "Frankfurt days 16-18 not satisfied"
        
        return {'itinerary': itinerary}
    else:
        return {"error": "No valid itinerary found"}

# Execute and print the result
result = solve_itinerary()
print(json.dumps(result, indent=2))