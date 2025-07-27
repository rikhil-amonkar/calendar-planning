from z3 import *
import json

def solve_itinerary():
    # Cities and their required visit durations
    cities = {
        'Riga': 2,
        'Frankfurt': 3,
        'Amsterdam': 2,
        'Vilnius': 5,
        'London': 2,
        'Stockholm': 3,
        'Bucharest': 4
    }
    
    # Direct flights between cities
    direct_flights = {
        'London': ['Amsterdam', 'Bucharest', 'Frankfurt', 'Stockholm'],
        'Amsterdam': ['London', 'Stockholm', 'Frankfurt', 'Riga', 'Vilnius', 'Bucharest'],
        'Vilnius': ['Frankfurt', 'Riga', 'Amsterdam'],
        'Riga': ['Vilnius', 'Stockholm', 'Frankfurt', 'Bucharest', 'Amsterdam'],
        'Frankfurt': ['Vilnius', 'Amsterdam', 'Stockholm', 'Riga', 'Bucharest', 'London'],
        'Stockholm': ['Riga', 'Amsterdam', 'Frankfurt', 'London'],
        'Bucharest': ['London', 'Riga', 'Frankfurt', 'Amsterdam']
    }

    # Create Z3 solver
    s = Solver()

    # Decision variables: city_day[c][d] is True if in city c on day d
    city_day = {city: [Bool(f"{city}_{day}") for day in range(1, 16)] for city in cities}

    # Constraint: Each day must be in exactly one city
    for day in range(1, 16):
        s.add(ExactlyOne([city_day[city][day-1] for city in cities]))

    # Constraint: Total days in each city must match requirements
    for city, days in cities.items():
        s.add(Sum([If(city_day[city][d], 1, 0) for d in range(15)]) == days)

    # Event constraints
    # Amsterdam visit between day 2 and 3 (must be in Amsterdam on day 2 or 3)
    s.add(Or(city_day['Amsterdam'][1], city_day['Amsterdam'][2]))

    # Workshop in Vilnius between day 7 and 11 (must be in Vilnius at least once during these days)
    s.add(Or([city_day['Vilnius'][d] for d in range(6, 11)]))

    # Wedding in Stockholm between day 13 and 15 (must be in Stockholm at least once during these days)
    s.add(Or([city_day['Stockholm'][d] for d in range(12, 15)]))

    # Flight constraints: If city changes between days, must have direct flight
    for day in range(1, 15):
        for c1 in cities:
            for c2 in cities:
                if c1 != c2:
                    # If we're in c1 on day and c2 on day+1, must have direct flight
                    s.add(Implies(
                        And(city_day[c1][day-1], city_day[c2][day]),
                        Or([c2 in direct_flights[c1]])
                    ))

    # Try to find a solution
    if s.check() == sat:
        model = s.model()
        itinerary = []
        
        # Build the itinerary day by day
        for day in range(1, 16):
            for city in cities:
                if is_true(model[city_day[city][day-1]]):
                    itinerary.append({"day": day, "place": city})
                    break
        
        # Verify the solution meets all constraints
        total_days = {city: 0 for city in cities}
        for entry in itinerary:
            total_days[entry['place']] += 1
        
        # Check duration constraints
        for city, days in cities.items():
            assert total_days[city] == days, f"Duration mismatch for {city}"
        
        # Check flight constraints
        for i in range(len(itinerary)-1):
            current = itinerary[i]['place']
            next_city = itinerary[i+1]['place']
            if current != next_city:
                assert next_city in direct_flights[current], f"No direct flight from {current} to {next_city}"
        
        return {"itinerary": itinerary}
    else:
        return {"error": "No valid itinerary found"}

# Execute and print the result
result = solve_itinerary()
print(json.dumps(result, indent=2))