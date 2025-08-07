from z3 import *
import json

def main():
    # Define the City type
    City = Datatype('City')
    City.declare('Valencia')
    City.declare('Athens')
    City.declare('Naples')
    City.declare('Zurich')
    City = City.create()
    Valencia, Athens, Naples, Zurich = City.Valencia, City.Athens, City.Naples, City.Zurich

    # Create variables for start and end cities for each day
    s = [Const('s_%d' % i, City) for i in range(20)]
    e = [Const('e_%d' % i, City) for i in range(20)]
    
    solver = Solver()
    
    # Allowed direct flights (directed edges)
    allowed_flights = [
        (Valencia, Naples),
        (Naples, Valencia),
        (Valencia, Athens),
        (Athens, Naples),
        (Naples, Athens),
        (Zurich, Naples),
        (Naples, Zurich),
        (Athens, Zurich),
        (Zurich, Athens),
        (Zurich, Valencia),
        (Valencia, Zurich)
    ]
    
    # Flight constraints: if start != end, the flight must be in allowed_flights
    for i in range(20):
        flight_taken = s[i] != e[i]
        allowed = Or([And(s[i] == c1, e[i] == c2) for (c1, c2) in allowed_flights])
        solver.add(Implies(flight_taken, allowed))
    
    # Consistency: start of day i is end of day i-1 for i>=1
    for i in range(1, 20):
        solver.add(s[i] == e[i-1])
    
    # Total days per city
    cities = [Valencia, Athens, Naples, Zurich]
    totals = [6, 6, 5, 6]
    for c, total in zip(cities, totals):
        count = 0
        for i in range(20):
            count += If(Or(s[i] == c, e[i] == c), 1, 0)
        solver.add(count == total)
    
    # Exactly 3 flight days (days with start != end)
    flight_days_count = Sum([If(s[i] != e[i], 1, 0) for i in range(20)])
    solver.add(flight_days_count == 3)
    
    # Athens must appear in days 1-6 (indices 0-5)
    solver.add(Or([Or(s[i] == Athens, e[i] == Athens) for i in range(0, 6)]))
    # Naples must appear in days 16-20 (indices 15-19)
    solver.add(Or([Or(s[i] == Naples, e[i] == Naples) for i in range(15, 20)]))
    
    # Solve the constraints
    if solver.check() == sat:
        model = solver.model()
        itinerary = []
        for i in range(20):
            start_val = model[s[i]]
            end_val = model[e[i]]
            # Convert to string representation
            if start_val == Valencia:
                start_city = "Valencia"
            elif start_val == Athens:
                start_city = "Athens"
            elif start_val == Naples:
                start_city = "Naples"
            else:  # Zurich
                start_city = "Zurich"
                
            if end_val == Valencia:
                end_city = "Valencia"
            elif end_val == Athens:
                end_city = "Athens"
            elif end_val == Naples:
                end_city = "Naples"
            else:  # Zurich
                end_city = "Zurich"
            
            if start_city == end_city:
                place_str = start_city
            else:
                place_str = f"{start_city},{end_city}"
            itinerary.append({"day": i+1, "place": place_str})
        
        result = {'itinerary': itinerary}
        print(json.dumps(result, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()