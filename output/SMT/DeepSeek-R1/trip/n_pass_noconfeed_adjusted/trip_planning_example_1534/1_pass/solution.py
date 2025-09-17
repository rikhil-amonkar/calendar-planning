import json
from z3 import *

def main():
    # City codes
    cities = ['Paris', 'Venice', 'Vilnius', 'Salzburg', 'Amsterdam', 'Barcelona', 'Hamburg', 'Florence', 'Tallinn', 'Warsaw']
    city_code = {city: idx for idx, city in enumerate(cities)}
    
    n_days = 25
    n_cities = len(cities)
    
    # Direct flights as city code pairs (unordered)
    direct_flights_list = [
        ('Paris', 'Venice'), ('Barcelona', 'Amsterdam'), ('Amsterdam', 'Warsaw'), ('Amsterdam', 'Vilnius'),
        ('Barcelona', 'Warsaw'), ('Warsaw', 'Venice'), ('Amsterdam', 'Hamburg'), ('Barcelona', 'Hamburg'),
        ('Barcelona', 'Florence'), ('Barcelona', 'Venice'), ('Paris', 'Hamburg'), ('Paris', 'Vilnius'),
        ('Paris', 'Amsterdam'), ('Paris', 'Florence'), ('Florence', 'Amsterdam'), ('Vilnius', 'Warsaw'),
        ('Barcelona', 'Tallinn'), ('Paris', 'Warsaw'), ('Tallinn', 'Warsaw'), ('Tallinn', 'Vilnius'),
        ('Amsterdam', 'Tallinn'), ('Paris', 'Tallinn'), ('Paris', 'Barcelona'), ('Venice', 'Hamburg'),
        ('Warsaw', 'Hamburg'), ('Hamburg', 'Salzburg'), ('Amsterdam', 'Venice')
    ]
    
    direct_flights_set = set()
    for (a, b) in direct_flights_list:
        code_a = city_code[a]
        code_b = city_code[b]
        direct_flights_set.add((min(code_a, code_b), max(code_a, code_b)))
    
    # Initialize Z3 solver
    solver = Solver()
    
    # Arrays for start and end city for each day (0-indexed days)
    start_city = [Int(f"start_{i}") for i in range(n_days)]
    end_city = [Int(f"end_{i}") for i in range(n_days)]
    
    # Constraint: start and end cities are within valid range
    for i in range(n_days):
        solver.add(start_city[i] >= 0, start_city[i] < n_cities)
        solver.add(end_city[i] >= 0, end_city[i] < n_cities)
    
    # Constraint: continuity between days
    for i in range(1, n_days):
        solver.add(start_city[i] == end_city[i-1])
    
    # Constraint: flight connectivity
    for i in range(n_days):
        # If start and end are different, there must be a direct flight
        a = start_city[i]
        b = end_city[i]
        solver.add(If(a != b, 
                      Or([And(min(a, b) == flight[0], max(a, b) == flight[1]) for flight in direct_flights_set]),
                      True))
    
    # Required days per city
    required_days = {
        'Warsaw': 4,
        'Venice': 3,
        'Vilnius': 3,
        'Salzburg': 4,
        'Amsterdam': 2,
        'Barcelona': 5,
        'Paris': 2,
        'Hamburg': 4,
        'Florence': 5,
        'Tallinn': 2
    }
    
    # Count total days per city
    for c_idx, city in enumerate(cities):
        total_days = Sum([If(Or(start_city[i] == c_idx, end_city[i] == c_idx), 1, 0) for i in range(n_days)])
        solver.add(total_days == required_days[city])
    
    # Specific constraints
    # Salzburg wedding between day 22 and 25 (index 21 to 24)
    solver.add(Or([Or(start_city[i] == city_code['Salzburg'], end_city[i] == city_code['Salzburg']) for i in range(21, 25)]))
    
    # Barcelona meeting between day 2 and 6 (index 1 to 5)
    solver.add(Or([Or(start_city[i] == city_code['Barcelona'], end_city[i] == city_code['Barcelona']) for i in range(1, 6)]))
    
    # Paris workshop between day 1 and 2 (index 0 to 1)
    solver.add(Or([Or(start_city[i] == city_code['Paris'], end_city[i] == city_code['Paris']) for i in range(0, 2)]))
    
    # Hamburg conference between day 19 and 22 (index 18 to 21)
    for i in range(18, 22):
        solver.add(Or(start_city[i] == city_code['Hamburg'], end_city[i] == city_code['Hamburg']))
    
    # Tallinn meeting between day 11 and 12 (index 10 to 11)
    solver.add(Or([Or(start_city[i] == city_code['Tallinn'], end_city[i] == city_code['Tallinn']) for i in range(10, 12)]))
    
    # Check feasibility
    if solver.check() == sat:
        model = solver.model()
        # Extract the start city for each day
        start_city_values = [model.evaluate(start_city[i]).as_long() for i in range(n_days)]
        
        # Group consecutive days with the same start city
        itinerary = []
        current_city = start_city_values[0]
        start_day = 0
        for day in range(1, n_days):
            if start_city_values[day] != current_city:
                end_day = day - 1
                itinerary.append({
                    "day_range": f"Day {start_day+1}-{end_day+1}",
                    "place": cities[current_city]
                })
                current_city = start_city_values[day]
                start_day = day
        itinerary.append({
            "day_range": f"Day {start_day+1}-{n_days}",
            "place": cities[current_city]
        })
        
        # Output as JSON
        print(json.dumps({"itinerary": itinerary}))
    else:
        print('{"itinerary": []}')

if __name__ == "__main__":
    main()