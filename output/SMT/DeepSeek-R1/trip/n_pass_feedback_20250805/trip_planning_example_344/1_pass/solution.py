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

    # Create variables for start and end cities for each day
    s = [Const('s_%d' % i, City) for i in range(20)]
    e = [Const('e_%d' % i, City) for i in range(20)]
    
    solver = Solver()
    
    # Allowed direct flights (directed edges)
    allowed_flights = [
        (City.Valencia, City.Naples),
        (City.Valencia, City.Athens),
        (City.Valencia, City.Zurich),
        (City.Naples, City.Valencia),
        (City.Naples, City.Athens),
        (City.Naples, City.Zurich),
        (City.Zurich, City.Valencia),
        (City.Zurich, City.Naples),
        (City.Zurich, City.Athens),
        (City.Athens, City.Naples),
        (City.Athens, City.Zurich)
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
    cities = [City.Valencia, City.Athens, City.Naples, City.Zurich]
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
    solver.add(Or([Or(s[i] == City.Athens, e[i] == City.Athens) for i in range(0, 6)]))
    # Naples must appear in days 16-20 (indices 15-19)
    solver.add(Or([Or(s[i] == City.Naples, e[i] == City.Naples) for i in range(15, 20)]))
    
    # Solve the constraints
    if solver.check() == sat:
        model = solver.model()
        city_names = {
            City.Valencia: "Valencia",
            City.Athens: "Athens",
            City.Naples: "Naples",
            City.Zurich: "Zurich"
        }
        itinerary = []
        for i in range(20):
            start_val = model[s[i]]
            end_val = model[e[i]]
            start_city = city_names[start_val.as_long()]
            end_city = city_names[end_val.as_long()]
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