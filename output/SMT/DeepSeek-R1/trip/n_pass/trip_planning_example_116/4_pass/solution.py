import z3
import json

def main():
    n_days = 18
    # Create day variables for days 0 to 17 (representing days 1 to 18)
    c = [z3.Int(f'c_{i}') for i in range(n_days)]
    solver = z3.Solver()
    
    # City encodings
    Split, London, Santorini = 0, 1, 2
    cities = [Split, London, Santorini]
    city_names = {Split: 'Split', London: 'London', Santorini: 'Santorini'}
    
    # Each day must be one of the three cities
    for i in range(n_days):
        solver.add(z3.Or([c[i] == city for city in cities]))
    
    # Start in Split on day 1 (index 0)
    solver.add(c[0] == Split)
    
    # Conference in Santorini on day 12 (index 11) and day 18 (index 17)
    solver.add(c[11] == Santorini)
    solver.add(c[17] == Santorini)
    
    # Flight constraints: only allow valid transitions
    for i in range(n_days - 1):
        solver.add(z3.Or(
            c[i] == c[i+1],  # Stay in the same city
            # Valid flights:
            z3.And(c[i] == Split, c[i+1] == London),
            z3.And(c[i] == London, c[i+1] == Split),
            z3.And(c[i] == London, c[i+1] == Santorini),
            z3.And(c[i] == Santorini, c[i+1] == London)
        ))
    
    # Count days in each city
    days_in_Split = z3.Sum([z3.If(c[i] == Split, 1, 0) for i in range(n_days)])
    days_in_London = z3.Sum([z3.If(c[i] == London, 1, 0) for i in range(n_days)])
    days_in_Santorini = z3.Sum([z3.If(c[i] == Santorini, 1, 0) for i in range(n_days)])
    
    # Add base day constraints (physical presence)
    solver.add(days_in_Split == 6)
    solver.add(days_in_London == 7)
    solver.add(days_in_Santorini == 5)
    
    # Solve and format the itinerary
    if solver.check() == z3.sat:
        model = solver.model()
        itinerary = []
        current_city = model.evaluate(c[0]).as_long()
        start_idx = 0
        for i in range(1, n_days):
            if model.evaluate(c[i]).as_long() != current_city:
                # Format day range: day_start to day_end (1-indexed)
                day_range = f"Day {start_idx+1}-{i}"
                itinerary.append({
                    'day_range': day_range,
                    'place': city_names[current_city]
                })
                current_city = model.evaluate(c[i]).as_long()
                start_idx = i
        # Add the last block
        day_range = f"Day {start_idx+1}-{n_days}"
        itinerary.append({
            'day_range': day_range,
            'place': city_names[current_city]
        })
        print(json.dumps({'itinerary': itinerary}))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()