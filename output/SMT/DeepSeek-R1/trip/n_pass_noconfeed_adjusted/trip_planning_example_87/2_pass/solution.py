import z3
import json

def main():
    # Define the city enum using EnumSort for better model interpretation
    CitySort, (riga, amsterdam, mykonos) = z3.EnumSort('City', ['riga', 'amsterdam', 'mykonos'])
    city_names = {
        riga: "Riga",
        amsterdam: "Amsterdam",
        mykonos: "Mykonos"
    }
    
    # Create arrays for morning (a) and evening (b) cities for each day (0-indexed for days 0-6)
    a = [z3.Const(f'a_{i+1}', CitySort) for i in range(7)]
    b = [z3.Const(f'b_{i+1}', CitySort) for i in range(7)]
    
    solver = z3.Solver()
    
    # Direct flight constraints
    def connected(c1, c2):
        return z3.Or(
            z3.And(c1 == riga, c2 == amsterdam),
            z3.And(c1 == amsterdam, c2 == riga),
            z3.And(c1 == amsterdam, c2 == mykonos),
            z3.And(c1 == mykonos, c2 == amsterdam)
        )
    
    # Evening city equals next morning city (b_i = a_{i+1})
    for i in range(6):
        solver.add(b[i] == a[i+1])
    
    # For each day, if morning and evening differ, require direct flight
    for i in range(7):
        solver.add(z3.Implies(a[i] != b[i], connected(a[i], b[i])))
    
    # Count days in each city (a day counts if either morning or evening is in the city)
    riga_days = [z3.Or(a[i] == riga, b[i] == riga) for i in range(7)]
    amsterdam_days = [z3.Or(a[i] == amsterdam, b[i] == amsterdam) for i in range(7)]
    mykonos_days = [z3.Or(a[i] == mykonos, b[i] == mykonos) for i in range(7)]
    
    solver.add(z3.Sum([z3.If(cond, 1, 0) for cond in riga_days]) == 2)
    solver.add(z3.Sum([z3.If(cond, 1, 0) for cond in amsterdam_days]) == 2)
    solver.add(z3.Sum([z3.If(cond, 1, 0) for cond in mykonos_days]) == 5)
    
    # Visit relatives in Riga on day 1 and day 2
    solver.add(z3.Or(a[0] == riga, b[0] == riga))  # Day 1
    solver.add(z3.Or(a[1] == riga, b[1] == riga))  # Day 2
    
    if solver.check() == z3.sat:
        model = solver.model()
        a_vals = []
        # Evaluate morning cities from the model
        for i in range(7):
            expr = a[i]
            interp = model[expr]
            # Map interpretation to city name
            if z3.eq(interp, riga):
                a_vals.append("Riga")
            elif z3.eq(interp, amsterdam):
                a_vals.append("Amsterdam")
            elif z3.eq(interp, mykonos):
                a_vals.append("Mykonos")
            else:
                # Fallback if unknown city
                a_vals.append("Unknown")
        
        # Generate itinerary by grouping consecutive days with same morning city
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
        
        print(json.dumps({"itinerary": itinerary}))
    else:
        print('{"itinerary": []}')

if __name__ == "__main__":
    main()