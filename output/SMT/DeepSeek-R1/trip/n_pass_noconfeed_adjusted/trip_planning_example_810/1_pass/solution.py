from z3 import *
import json

def main():
    # Define cities and their indices
    cities = ['Berlin', 'Nice', 'Athens', 'Stockholm', 'Barcelona', 'Vilnius', 'Lyon']
    city_index = {city: idx for idx, city in enumerate(cities)}
    
    # Direct flights as list of tuples
    direct_flights = [
        ('Lyon', 'Nice'),
        ('Stockholm', 'Athens'),
        ('Nice', 'Athens'),
        ('Berlin', 'Athens'),
        ('Berlin', 'Nice'),
        ('Berlin', 'Barcelona'),
        ('Berlin', 'Vilnius'),
        ('Barcelona', 'Nice'),
        ('Athens', 'Vilnius'),
        ('Berlin', 'Stockholm'),
        ('Nice', 'Stockholm'),
        ('Barcelona', 'Athens'),
        ('Barcelona', 'Stockholm'),
        ('Barcelona', 'Lyon')
    ]
    
    # Create allowed flights as sets of city indices
    allowed_flights_set = set()
    for city1, city2 in direct_flights:
        idx1, idx2 = city_index[city1], city_index[city2]
        allowed_flights_set.add(frozenset({idx1, idx2}))
    
    # Create allowed tuples for Z3 constraints (both directions)
    allowed_tuples = []
    for flight in allowed_flights_set:
        i, j = tuple(flight)
        allowed_tuples.append((i, j))
        allowed_tuples.append((j, i))
    
    # Initialize Z3 solver
    solver = Solver()
    
    # Define overnight variables for 21 days (index 0 to 20)
    overnight = [Int(f'overnight_{i}') for i in range(21)]
    
    # Add constraints for overnight variables to be within valid city indices
    for i in range(21):
        solver.add(overnight[i] >= 0, overnight[i] < len(cities))
    
    # Constraint: Start in Berlin
    solver.add(overnight[0] == city_index['Berlin'])
    
    # Constraints for direct flights between consecutive days
    for d in range(1, 21):
        city_prev = overnight[d-1]
        city_curr = overnight[d]
        # If cities are different, ensure there is a direct flight
        flight_constraint = Or([And(city_prev == i, city_curr == j) for i, j in allowed_tuples])
        solver.add(If(city_prev != city_curr, flight_constraint, True))
    
    # Constraints for total days in each city
    total_days = [0] * len(cities)
    for c_idx in range(len(cities)):
        total_days[c_idx] = Sum([
            If(Or(overnight[d-1] == c_idx, overnight[d] == c_idx), 1, 0)
            for d in range(1, 21)
        ])
    
    solver.add(total_days[city_index['Berlin']] == 3)
    solver.add(total_days[city_index['Nice']] == 5)
    solver.add(total_days[city_index['Athens']] == 5)
    solver.add(total_days[city_index['Stockholm']] == 5)
    solver.add(total_days[city_index['Barcelona']] == 2)
    solver.add(total_days[city_index['Vilnius']] == 4)
    solver.add(total_days[city_index['Lyon']] == 2)
    
    # Constraints for fixed events
    # Day 3: Must be in Berlin and Barcelona
    solver.add(Or(overnight[2] == city_index['Berlin'], overnight[3] == city_index['Berlin']))
    solver.add(Or(overnight[2] == city_index['Barcelona'], overnight[3] == city_index['Barcelona']))
    # Day 4: Must be in Barcelona and Lyon
    solver.add(Or(overnight[3] == city_index['Barcelona'], overnight[4] == city_index['Barcelona']))
    solver.add(Or(overnight[3] == city_index['Lyon'], overnight[4] == city_index['Lyon']))
    # Day 5: Must be in Lyon
    solver.add(Or(overnight[4] == city_index['Lyon'], overnight[5] == city_index['Lyon']))
    
    # Check satisfiability
    if solver.check() == sat:
        model = solver.model()
        # Extract overnight values
        overnight_values = [model.evaluate(overnight[i]).as_long() for i in range(21)]
        
        # Generate itinerary
        itinerary = []
        current_city = overnight_values[0]
        start_day = 1
        for d in range(1, 21):
            if overnight_values[d] != current_city:
                end_day = d
                itinerary.append({
                    "day_range": f"Day {start_day}-{end_day}",
                    "place": cities[current_city]
                })
                start_day = d
                current_city = overnight_values[d]
        itinerary.append({
            "day_range": f"Day {start_day}-20",
            "place": cities[current_city]
        })
        
        # Output as JSON
        print(json.dumps({"itinerary": itinerary}))
    else:
        print('{"itinerary": []}')

if __name__ == "__main__":
    main()