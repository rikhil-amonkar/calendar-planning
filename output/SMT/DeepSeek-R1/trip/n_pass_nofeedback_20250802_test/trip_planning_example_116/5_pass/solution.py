import z3
import json

def main():
    n_days = 18
    c = [z3.Int(f'c_{i}') for i in range(n_days)]
    solver = z3.Solver()
    
    Split, London, Santorini = 0, 1, 2
    city_names = {Split: 'Split', London: 'London', Santorini: 'Santorini'}
    
    # Start in Split on day 1 (index 0)
    solver.add(c[0] == Split)
    
    # Conference in Santorini on day 12 (index 11) and day 18 (index 17)
    solver.add(c[11] == Santorini)
    solver.add(c[17] == Santorini)
    
    # Each day must be one of the three cities
    for i in range(n_days):
        solver.add(z3.Or(c[i] == Split, c[i] == London, c[i] == Santorini))
    
    # Flight transitions: only between Split and London, or London and Santorini
    for i in range(n_days - 1):
        solver.add(z3.Or(
            c[i] == c[i+1],  # Stay in the same city
            z3.And(c[i] == Split, c[i+1] == London),
            z3.And(c[i] == London, c[i+1] == Split),
            z3.And(c[i] == London, c[i+1] == Santorini),
            z3.And(c[i] == Santorini, c[i+1] == London)
        ))
    
    # No consecutive flights: if flight on day i, then must stay in the next city on day i+1 and i+2
    for i in range(n_days - 2):
        solver.add(z3.Or(
            c[i] == c[i+1],  # No flight on day i
            c[i+1] == c[i+2]  # After flight on day i, stay in the same city on day i+1 and i+2
        ))
    
    # Base days: 6 in Split, 7 in London, 5 in Santorini
    days_in_Split = z3.Sum([z3.If(c[i] == Split, 1, 0) for i in range(n_days)])
    days_in_London = z3.Sum([z3.If(c[i] == London, 1, 0) for i in range(n_days)])
    days_in_Santorini = z3.Sum([z3.If(c[i] == Santorini, 1, 0) for i in range(n_days)])
    
    solver.add(days_in_Split == 6)
    solver.add(days_in_London == 7)
    solver.add(days_in_Santorini == 5)
    
    if solver.check() == z3.sat:
        model = solver.model()
        itinerary = []
        current_city = model.evaluate(c[0]).as_long()
        start_idx = 0
        for i in range(1, n_days):
            city_val = model.evaluate(c[i]).as_long()
            if city_val != current_city:
                day_range = f"Day {start_idx+1}-{i}"
                itinerary.append({
                    'day_range': day_range,
                    'place': city_names[current_city]
                })
                current_city = city_val
                start_idx = i
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