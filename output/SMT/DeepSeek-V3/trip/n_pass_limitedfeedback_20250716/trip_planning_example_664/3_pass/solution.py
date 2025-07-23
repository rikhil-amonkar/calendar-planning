from z3 import *

def solve_itinerary():
    # Cities and their required days
    cities = {
        'Tallinn': 2,
        'Bucharest': 4,
        'Seville': 5,
        'Stockholm': 5,
        'Munich': 5,
        'Milan': 2
    }
    
    # Direct flights as adjacency list
    direct_flights = {
        'Milan': ['Stockholm', 'Munich', 'Seville'],
        'Stockholm': ['Milan', 'Munich', 'Tallinn'],
        'Munich': ['Stockholm', 'Bucharest', 'Seville', 'Milan', 'Tallinn'],
        'Bucharest': ['Munich'],
        'Seville': ['Munich', 'Milan'],
        'Tallinn': ['Stockholm', 'Munich']
    }
    
    # Create a solver instance
    solver = Solver()
    
    # Create variables for each day (1..18) representing the city
    days = [Int(f'day_{i}') for i in range(1, 19)]
    
    # Each day's variable must correspond to a city (encoded as integers)
    city_ids = {
        'Tallinn': 0,
        'Bucharest': 1,
        'Seville': 2,
        'Stockholm': 3,
        'Munich': 4,
        'Milan': 5
    }
    id_to_city = {v: k for k, v in city_ids.items()}
    
    # Add constraints that each day's value is a valid city ID
    for day in days:
        solver.add(Or([day == city_ids[city] for city in cities]))
    
    # Constraint: Total days per city must match the required days
    for city, required_days in cities.items():
        solver.add(Sum([If(day == city_ids[city], 1, 0) for day in days]) == required_days)
    
    # Constraint: Transitions between cities must be via direct flights
    for i in range(17):  # days 1..17 and next day is i+2 (0-based)
        current_day = days[i]
        next_day = days[i+1]
        # Either stay in the same city or move to a directly connected city
        solver.add(Or(
            current_day == next_day,
            *[
                And(current_day == city_ids[city], next_day == city_ids[neighbor])
                for city in direct_flights
                for neighbor in direct_flights[city]
            ]
        ))
    
    # Special constraints:
    # Bucharest's 4 days must be within days 1-4
    solver.add(Sum([If(days[i] == city_ids['Bucharest'], 1, 0) for i in range(4)]) == 4)
    
    # Munich's 5 days must be within days 4-8
    solver.add(Sum([If(days[i] == city_ids['Munich'], 1, 0) for i in range(3, 8)]) == 5)
    
    # Seville's 5 days must be within days 8-12
    solver.add(Sum([If(days[i] == city_ids['Seville'], 1, 0) for i in range(7, 12)]) == 5)
    
    # Check if the solver can find a solution
    if solver.check() == sat:
        model = solver.model()
        itinerary = []
        for i in range(18):
            day_num = i + 1
            city_id = model.evaluate(days[i]).as_long()
            city = id_to_city[city_id]
            itinerary.append({"day": day_num, "place": city})
        
        # Prepare the output
        output = {
            "itinerary": itinerary
        }
        return output
    else:
        return {"error": "No valid itinerary found"}

# Generate the itinerary
itinerary = solve_itinerary()
print(itinerary)