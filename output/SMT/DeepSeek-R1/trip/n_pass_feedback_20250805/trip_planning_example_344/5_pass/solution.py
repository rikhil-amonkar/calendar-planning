from z3 import *
import json

def main():
    City = Datatype('City')
    City.declare('Valencia')
    City.declare('Athens')
    City.declare('Naples')
    City.declare('Zurich')
    City = City.create()
    Valencia, Athens, Naples, Zurich = City.Valencia, City.Athens, City.Naples, City.Zurich

    s = [Const('s_%d' % i, City) for i in range(20)]
    e = [Const('e_%d' % i, City) for i in range(20)]
    
    solver = Solver()
    
    # Symmetry-breaking constraints
    solver.add(s[0] == Athens)  # Start in Athens
    solver.add(e[19] == Naples)  # End in Naples
    # Force early flight within first 4 days
    solver.add(Or(s[0] != e[0], s[1] != e[1], s[2] != e[2], s[3] != e[3]))
    
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
    
    for i in range(20):
        flight_taken = s[i] != e[i]
        allowed = Or([And(s[i] == c1, e[i] == c2) for (c1, c2) in allowed_flights])
        solver.add(Implies(flight_taken, allowed))
    
    for i in range(1, 20):
        solver.add(e[i-1] == s[i])
    
    cities = [Valencia, Athens, Naples, Zurich]
    totals = [6, 6, 5, 6]
    for c, total in zip(cities, totals):
        count = 0
        for i in range(20):
            count += If(Or(s[i] == c, e[i] == c), 1, 0)
        solver.add(count == total)
    
    flight_days_count = Sum([If(s[i] != e[i], 1, 0) for i in range(20)])
    solver.add(flight_days_count == 3)
    
    solver.add(Or([Or(s[i] == Athens, e[i] == Athens) for i in range(0, 6)]))
    solver.add(Or([Or(s[i] == Naples, e[i] == Naples) for i in range(15, 20)]))
    
    if solver.check() == sat:
        model = solver.model()
        itinerary = []
        city_names = {
            Valencia: "Valencia",
            Athens: "Athens",
            Naples: "Naples",
            Zurich: "Zurich"
        }
        for i in range(20):
            start_val = model[s[i]]
            end_val = model[e[i]]
            start_city = city_names[start_val]
            end_city = city_names[end_val]
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