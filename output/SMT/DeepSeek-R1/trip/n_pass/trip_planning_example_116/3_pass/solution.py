import z3
import json

def main():
    n_days = 18
    c = [z3.Int(f'c_{i}') for i in range(n_days)]
    solver = z3.Solver()
    
    # City encoding
    Split, Santorini, London = 0, 1, 2
    cities = [Split, Santorini, London]
    city_names = {Split: 'Split', Santorini: 'Santorini', London: 'London'}
    
    # Each day must be one of the cities
    for i in range(n_days):
        solver.add(z3.Or([c[i] == city for city in cities]))
    
    # Conference constraints: Santorini on day 12 (index 11) and day 18 (index 17)
    solver.add(c[11] == Santorini)
    solver.add(c[17] == Santorini)
    
    # Santorini block: days 12-18 (indices 11-17)
    for i in range(11, n_days):
        solver.add(c[i] == Santorini)
    
    # No Santorini before day 12 (indices 0-10)
    for i in range(0, 11):
        solver.add(c[i] != Santorini)
    
    # Start in Split on day 1 (index 0)
    solver.add(c[0] == Split)
    
    # Flight constraints: only valid transitions
    for i in range(1, n_days):
        solver.add(z3.Implies(
            c[i-1] != c[i],
            z3.Or(
                z3.And(c[i-1] == Split, c[i] == London),
                z3.And(c[i-1] == London, c[i] == Split),
                z3.And(c[i-1] == London, c[i] == Santorini),
                z3.And(c[i-1] == Santorini, c[i] == London)
            )
        ))
    
    # Count base days in each city
    base_days = [z3.Sum([z3.If(c[i] == city, 1, 0) for i in range(n_days)]) 
                 for city in cities]
    
    # Count flight departures for each city
    departures = [
        z3.Sum([
            z3.If(z3.And(c[i-1] == city, c[i] != city), 1, 0)
            for i in range(1, n_days)
        ]) for city in cities
    ]
    
    # Total days = base days + departures
    total_Split = base_days[Split] + departures[Split]
    total_London = base_days[London] + departures[London]
    total_Santorini = base_days[Santorini]  # No departures from Santorini
    
    # Apply day constraints
    solver.add(total_Split == 6)
    solver.add(total_London == 7)
    solver.add(total_Santorini == 7)
    
    # Must be in London on day 11 (index 10) to fly to Santorini on day 12
    solver.add(c[10] == London)
    
    # Solve and output
    if solver.check() == z3.sat:
        model = solver.model()
        itinerary = []
        current_city = model.evaluate(c[0]).as_long()
        start_day = 1
        for i in range(1, n_days):
            city_val = model.evaluate(c[i]).as_long()
            if city_val != current_city:
                end_day = i
                itinerary.append({
                    'day_range': f'Day {start_day}-{end_day}',
                    'place': city_names[current_city]
                })
                start_day = i + 1
                current_city = city_val
        itinerary.append({
            'day_range': f'Day {start_day}-{n_days}',
            'place': city_names[current_city]
        })
        print(json.dumps({'itinerary': itinerary}))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()