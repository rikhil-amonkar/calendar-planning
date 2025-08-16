from z3 import *

def main():
    # Define the cities as an EnumSort
    City, (Reykjavik, Riga, Warsaw, Istanbul, Krakow) = EnumSort('City', ['Reykjavik', 'Riga', 'Warsaw', 'Istanbul', 'Krakow'])
    
    # Create variables for the itinerary: 5 cities
    cities = [Const(f'city_{i}', City) for i in range(5)]
    
    solver = Solver()
    
    # First city is Riga
    solver.add(cities[0] == Riga)
    
    # All cities are distinct
    for i in range(5):
        for j in range(i+1, 5):
            solver.add(cities[i] != cities[j])
    
    # Allowed direct flights
    allowed_flights = [
        (Reykjavik, Warsaw),
        (Warsaw, Reykjavik),
        (Istanbul, Warsaw),
        (Warsaw, Istanbul),
        (Riga, Istanbul),
        (Istanbul, Riga),
        (Riga, Warsaw),
        (Warsaw, Riga),
        (Istanbul, Krakow),
        (Krakow, Istanbul),
        (Krakow, Warsaw),
        (Warsaw, Krakow),
    ]
    
    # Add constraints for transitions between consecutive cities
    for i in range(4):
        current = cities[i]
        next_city = cities[i+1]
        constraints = []
        for a, b in allowed_flights:
            constraints.append(And(current == a, next_city == b))
        solver.add(Or(constraints))
    
    # Compute start_days
    start_days = [Int(f'start_day_{i}') for i in range(5)]
    solver.add(start_days[0] == 1)
    
    for i in range(1, 5):
        prev_city = cities[i-1]
        # Determine the duration of the previous city
        duration = If(prev_city == Reykjavik, 7,
                      If(prev_city == Riga, 2,
                         If(prev_city == Warsaw, 3,
                            If(prev_city == Istanbul, 6, 7))))
        solver.add(start_days[i] == start_days[i-1] + duration - 1)
    
    # Ensure Istanbul's start_day is <=7
    for m in range(5):
        solver.add(Implies(cities[m] == Istanbul, start_days[m] <= 7))
    
    # Check if the solver can find a solution
    if solver.check() == sat:
        model = solver.model()
        
        # Extract the itinerary order
        itinerary_order = [model.evaluate(cities[i]) for i in range(5)]
        start_days_values = [model.evaluate(start_days[i]).as_long() for i in range(5)]
        
        # Generate the day-place mappings
        result = {}
        for i in range(5):
            city = itinerary_order[i]
            s_day = start_days_values[i]
            if city == Reykjavik:
                duration = 7
            elif city == Riga:
                duration = 2
            elif city == Warsaw:
                duration = 3
            elif city == Istanbul:
                duration = 6
            elif city == Krakow:
                duration = 7
            end_day = s_day + duration - 1
            for day in range(s_day, end_day + 1):
                result[day] = city.name()
        
        # Sort the days and create the JSON output
        sorted_days = sorted(result.items())
        itinerary = [{'day': day, 'city': city} for day, city in sorted_days]
        
        # Print the JSON
        import json
        print(json.dumps({'itinerary': itinerary}, indent=2))
    else:
        print("No solution found.")

if __name__ == "__main__":
    main()