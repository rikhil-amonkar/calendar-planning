from z3 import *
import json

def main():
    # Create solver
    s = Solver()
    
    # Days and cities
    days = 12
    cities = ['Prague', 'Berlin', 'Tallinn', 'Stockholm']
    city_idx = {c: i for i, c in enumerate(cities)}
    
    # Presence matrix: presents[d][c] is True if we are in city c on day d
    presents = [[Bool(f"day_{d}_city_{c}") for c in range(len(cities))] for d in range(days)]
    
    # Constraints for each day: at least one city, at most two cities
    for d in range(days):
        s.add(Or([presents[d][c] for c in range(len(cities))]))
        s.add(Sum([If(presents[d][c], 1, 0) for c in range(len(cities))]) <= 2)
    
    # Fixed constraints
    # Day 6 (index 5) must be in Berlin
    s.add(presents[5][city_idx['Berlin']])
    # Day 8 (index 7) must be in Berlin and Tallinn
    s.add(presents[7][city_idx['Berlin']])
    s.add(presents[7][city_idx['Tallinn']])
    # Days 9-12 (indices 8 to 11) must be in Tallinn
    for d in range(8, 12):
        s.add(presents[d][city_idx['Tallinn']])
    
    # Total days per city
    total_days = [
        ('Prague', 2),
        ('Berlin', 3),
        ('Tallinn', 5),
        ('Stockholm', 5)
    ]
    for city, total in total_days:
        idx = city_idx[city]
        s.add(Sum([If(presents[d][idx], 1, 0) for d in range(days)]) == total)
    
    # Direct flights set (using city indices)
    direct_flights = set([
        (min(city_idx['Berlin'], city_idx['Tallinn']), max(city_idx['Berlin'], city_idx['Tallinn'])),
        (min(city_idx['Prague'], city_idx['Tallinn']), max(city_idx['Prague'], city_idx['Tallinn'])),
        (min(city_idx['Stockholm'], city_idx['Tallinn']), max(city_idx['Stockholm'], city_idx['Tallinn'])),
        (min(city_idx['Prague'], city_idx['Stockholm']), max(city_idx['Prague'], city_idx['Stockholm'])),
        (min(city_idx['Stockholm'], city_idx['Berlin']), max(city_idx['Stockholm'], city_idx['Berlin']))
    ])
    
    # Function to check if two cities are connected
    def are_connected(i, j):
        if i == j:
            return True
        pair = (min(i, j), max(i, j))
        return pair in direct_flights
    
    # Constraints for continuity and flights
    for d in range(days - 1):
        # If a city is new on day d+1, then day d must be a flight day and the new city must be connected to one of the cities on day d
        for c in range(len(cities)):
            # City c is new on day d+1 if it is present on d+1 but not on d
            new_city = And(presents[d+1][c], Not(presents[d][c]))
            # If there is a new city, then day d must have exactly two cities (flight day)
            s.add(Implies(new_city, Sum([If(presents[d][c2], 1, 0) for c2 in range(len(cities))]) == 2))
            # And there must be a city c2 on day d that is connected to c
            s.add(Implies(new_city, Or([And(presents[d][c2], are_connected(c2, c)) for c2 in range(len(cities))])))
        
        # Every day with two cities must have connected cities
        two_cities = Sum([If(presents[d][c], 1, 0) for c in range(len(cities))]) == 2
        # Find the two cities and ensure they are connected
        for c1 in range(len(cities)):
            for c2 in range(c1+1, len(cities)):
                s.add(Implies(And(two_cities, presents[d][c1], presents[d][c2]), are_connected(c1, c2)))
    
    # Check for feasibility
    if s.check() == sat:
        m = s.model()
        # Determine the primary city for each day (first city that is present)
        primary_cities = []
        for d in range(days):
            found = False
            for c in range(len(cities)):
                if is_true(m.evaluate(presents[d][c])):
                    primary_cities.append(cities[c])
                    found = True
                    break
            if not found:
                # Fallback: use the first city if no city is found (should not happen due to constraints)
                primary_cities.append(cities[0])
        
        # Group consecutive days with the same primary city
        itinerary = []
        start_day = 0
        current_city = primary_cities[0]
        for d in range(1, days):
            if primary_cities[d] != current_city:
                end_day = d
                itinerary.append({
                    "day_range": f"Day {start_day+1}-{end_day}",
                    "place": current_city
                })
                start_day = d
                current_city = primary_cities[d]
        itinerary.append({
            "day_range": f"Day {start_day+1}-{days}",
            "place": current_city
        })
        
        # Output as JSON
        print(json.dumps({"itinerary": itinerary}))
    else:
        print('{"itinerary": []}')

if __name__ == "__main__":
    main()