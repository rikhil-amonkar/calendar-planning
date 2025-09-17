import z3
import json

def main():
    # Define the city enum
    CitySort = z3.DeclareSort('City')
    riga, amsterdam, mykonos = z3.Consts('riga amsterdam mykonos', CitySort)
    cities = [riga, amsterdam, mykonos]
    city_names = {riga: "Riga", amsterdam: "Amsterdam", mykonos: "Mykonos"}
    
    # Create arrays for morning (a) and evening (b) cities for each day (1-indexed, days 1 to 7)
    a = [z3.Const(f'a_{i}', CitySort) for i in range(1, 8)]
    b = [z3.Const(f'b_{i}', CitySort) for i in range(1, 8)]
    
    solver = z3.Solver()
    
    # Direct flight constraints: only between Amsterdam-Mykonos and Riga-Amsterdam
    def connected(c1, c2):
        return z3.Or(
            z3.And(c1 == riga, c2 == amsterdam),
            z3.And(c1 == amsterdam, c2 == riga),
            z3.And(c1 == amsterdam, c2 == mykonos),
            z3.And(c1 == mykonos, c2 == amsterdam)
        )
    
    # Consistency constraint: evening city equals next morning city
    for i in range(1, 7):
        solver.add(b[i-1] == a[i])
    
    # For each day, if morning and evening cities are different, they must be connected by a direct flight
    for i in range(1, 8):
        solver.add(z3.Implies(a[i-1] != b[i-1], connected(a[i-1], b[i-1])))
    
    # Count days in each city (a day counts for a city if either morning or evening is that city)
    riga_days = [z3.Or(a[i] == riga, b[i] == riga) for i in range(0, 7)]
    amsterdam_days = [z3.Or(a[i] == amsterdam, b[i] == amsterdam) for i in range(0, 7)]
    mykonos_days = [z3.Or(a[i] == mykonos, b[i] == mykonos) for i in range(0, 7)]
    
    solver.add(z3.Sum([z3.If(cond, 1, 0) for cond in riga_days]) == 2)
    solver.add(z3.Sum([z3.If(cond, 1, 0) for cond in amsterdam_days]) == 2)
    solver.add(z3.Sum([z3.If(cond, 1, 0) for cond in mykonos_days]) == 5)
    
    # Constraint: visit relatives in Riga between day 1 and day 2 (must be in Riga on day 1 and day 2)
    solver.add(z3.Or(a[0] == riga, b[0] == riga))  # Day 1
    solver.add(z3.Or(a[1] == riga, b[1] == riga))  # Day 2
    
    # Check satisfiability
    if solver.check() == z3.sat:
        model = solver.model()
        
        # Interpret morning cities from the model
        a_vals = []
        for i in range(7):
            city_val = model.evaluate(a[i])
            for city in cities:
                if z3.eq(city_val, city):
                    a_vals.append(city_names[city])
                    break
        
        # Group consecutive days with the same morning city
        itinerary = []
        current_city = a_vals[0]
        start_day = 1
        for day in range(1, 7):
            if a_vals[day] != current_city:
                end_day = day
                itinerary.append({
                    "day_range": f"Day {start_day}-{end_day}",
                    "place": current_city
                })
                start_day = day + 1
                current_city = a_vals[day]
        itinerary.append({
            "day_range": f"Day {start_day}-7",
            "place": current_city
        })
        
        # Output as JSON
        print(json.dumps({"itinerary": itinerary}))
    else:
        print('{"itinerary": []}')

if __name__ == "__main__":
    main()