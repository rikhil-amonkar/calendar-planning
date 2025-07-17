import json
from z3 import *

def solve_itinerary():
    # Cities and their required days
    cities = {
        'Santorini': 5,
        'Krakow': 5,
        'Paris': 5,
        'Vilnius': 3,
        'Munich': 5,
        'Geneva': 2,
        'Amsterdam': 4,
        'Budapest': 5,
        'Split': 4
    }
    
    # Direct flights as a set of tuples (from, to)
    direct_flights = {
        ('Paris', 'Krakow'), ('Krakow', 'Paris'),
        ('Paris', 'Amsterdam'), ('Amsterdam', 'Paris'),
        ('Paris', 'Split'), ('Split', 'Paris'),
        ('Vilnius', 'Munich'), ('Munich', 'Vilnius'),
        ('Paris', 'Geneva'), ('Geneva', 'Paris'),
        ('Amsterdam', 'Geneva'), ('Geneva', 'Amsterdam'),
        ('Munich', 'Split'), ('Split', 'Munich'),
        ('Split', 'Krakow'), ('Krakow', 'Split'),
        ('Munich', 'Amsterdam'), ('Amsterdam', 'Munich'),
        ('Budapest', 'Amsterdam'), ('Amsterdam', 'Budapest'),
        ('Split', 'Geneva'), ('Geneva', 'Split'),
        ('Vilnius', 'Split'), ('Split', 'Vilnius'),
        ('Munich', 'Geneva'), ('Geneva', 'Munich'),
        ('Munich', 'Krakow'), ('Krakow', 'Munich'),
        ('Krakow', 'Vilnius'), ('Vilnius', 'Krakow'),
        ('Vilnius', 'Amsterdam'), ('Amsterdam', 'Vilnius'),
        ('Budapest', 'Paris'), ('Paris', 'Budapest'),
        ('Krakow', 'Amsterdam'), ('Amsterdam', 'Krakow'),
        ('Vilnius', 'Paris'), ('Paris', 'Vilnius'),
        ('Budapest', 'Geneva'), ('Geneva', 'Budapest'),
        ('Split', 'Amsterdam'), ('Amsterdam', 'Split'),
        ('Santorini', 'Geneva'), ('Geneva', 'Santorini'),
        ('Amsterdam', 'Santorini'), ('Santorini', 'Amsterdam'),
        ('Munich', 'Budapest'), ('Budapest', 'Munich'),
        ('Munich', 'Paris'), ('Paris', 'Munich')
    }
    
    # Create a sorted list of city names
    city_list = sorted(cities.keys())
    city_to_idx = {city: idx for idx, city in enumerate(city_list)}
    
    # Create Z3 variables: day[i] is the city visited on day i+1 (days are 1-based)
    days = [Int(f'day_{i}') for i in range(30)]
    
    # Solver instance
    solver = Solver()
    
    # Each day must be a valid city index (0 to 8)
    for day in days:
        solver.add(day >= 0, day < len(city_list))
    
    # Function to get city index by name
    def city_index(city_name):
        return city_to_idx[city_name]
    
    # Constraints for specific date ranges:
    # Santorini between day 25 and 29 (inclusive)
    solver.add(Or(*[days[i] == city_index('Santorini') for i in range(24, 29)]))  # days 25-29 are indices 24-28
    
    # Krakow wedding between day 18 and 22
    solver.add(Or(*[days[i] == city_index('Krakow') for i in range(17, 22)]))  # days 18-22 are indices 17-21
    
    # Paris friend meeting between day 11 and 15
    solver.add(Or(*[days[i] == city_index('Paris') for i in range(10, 15)]))  # days 11-15 are indices 10-14
    
    # Constraints for total days in each city
    for city, total_days in cities.items():
        idx = city_index(city)
        solver.add(Sum([If(day == idx, 1, 0) for day in days]) == total_days)
    
    # Flight constraints: consecutive days can only change to directly connected cities
    for i in range(29):  # from day 1 to 29 (0-based 0 to 28)
        current_day = days[i]
        next_day = days[i+1]
        # Either stay in the same city or move to a directly connected city
        solver.add(Or(
            current_day == next_day,
            *[
                And(current_day == city_index(from_city), next_day == city_index(to_city))
                for (from_city, to_city) in direct_flights
                if from_city in city_to_idx and to_city in city_to_idx
            ]
        ))
    
    # Check if the problem is satisfiable
    if solver.check() == sat:
        model = solver.model()
        itinerary = []
        for day_num in range(1, 31):
            city_idx = model.evaluate(days[day_num - 1]).as_long()
            city = city_list[city_idx]
            itinerary.append({"day": day_num, "place": city})
        
        # Verify the solution meets all constraints
        itinerary_json = {"itinerary": itinerary}
        return itinerary_json
    else:
        return {"error": "No valid itinerary found"}

# Generate the itinerary
itinerary = solve_itinerary()
print(json.dumps(itinerary, indent=2))