from z3 import *
import json

def main():
    # City indices
    cities = ['Oslo', 'Helsinki', 'Edinburgh', 'Riga', 'Tallinn', 'Budapest', 'Vilnius', 'Porto', 'Geneva']
    n_days = 25
    n_cities = len(cities)
    
    # Required days per city
    req_days = [2, 2, 3, 2, 5, 5, 5, 5, 4]
    
    # Direct flights (city indices, ensuring a < b)
    flights_list = [
        (7, 0), (2, 5), (2, 8), (3, 4), (2, 7), (6, 1), (4, 6), (3, 0), (8, 0),
        (2, 0), (2, 1), (6, 0), (3, 1), (5, 8), (1, 5), (1, 0), (2, 3), (4, 1),
        (8, 7), (5, 0), (1, 8), (3, 6), (4, 0)
    ]
    flights_set = set(flights_list)
    
    # Create solver and variables
    solver = Solver()
    in_days = [[Bool(f"in_{day}_{city}") for city in range(n_cities)] for day in range(n_days)]
    
    # Constraint 1: Each day must have at least one and at most two cities
    for day in range(n_days):
        solver.add(Or(in_days[day]))  # Replaced AtLeastOne with Or
        solver.add(Sum([If(in_days[day][city], 1, 0) for city in range(n_cities)]) <= 2)
    
    # Constraint 2: If two cities on same day, they must be connected by direct flight
    for day in range(n_days):
        for city1 in range(n_cities):
            for city2 in range(city1 + 1, n_cities):
                if (city1, city2) not in flights_set:
                    solver.add(Not(And(in_days[day][city1], in_days[day][city2])))
    
    # Constraint 3: Total days per city must match requirements
    for city in range(n_cities):
        total_days = Sum([If(in_days[day][city], 1, 0) for day in range(n_days)])
        solver.add(total_days == req_days[city])
    
    # Constraint 4: Consecutive days must share at least one city
    for day in range(n_days - 1):
        solver.add(Or([And(in_days[day][city], in_days[day + 1][city]) for city in range(n_cities)]))
    
    # Constraint 5: Wedding in Tallinn between days 4-8 (1-indexed -> 3-7 0-indexed)
    solver.add(Or([in_days[day][4] for day in range(3, 8)]))
    
    # Constraint 6: Meeting in Oslo between days 24-25 (1-indexed -> 23-24 0-indexed)
    solver.add(Or(in_days[23][0], in_days[24][0]))
    
    # Solve the constraints
    if solver.check() == sat:
        model = solver.model()
        itinerary = []
        current_start = 0
        current_places = set()
        
        # Get the set of cities for each day from the model
        day_places = []
        for day in range(n_days):
            places = set()
            for city in range(n_cities):
                if is_true(model.evaluate(in_days[day][city])):
                    places.add(cities[city])
            day_places.append(places)
        
        # Group consecutive days with the same set of cities
        for day in range(1, n_days):
            if day_places[day] != day_places[current_start]:
                places_str = " and ".join(sorted(day_places[current_start]))
                itinerary.append({
                    "day_range": f"Day {current_start + 1}-{day}",
                    "place": places_str
                })
                current_start = day
        # Add the last segment
        places_str = " and ".join(sorted(day_places[current_start]))
        itinerary.append({
            "day_range": f"Day {current_start + 1}-{n_days}",
            "place": places_str
        })
        
        print(json.dumps({"itinerary": itinerary}))
    else:
        print('{"error": "No valid itinerary found"}')

if __name__ == "__main__":
    main()