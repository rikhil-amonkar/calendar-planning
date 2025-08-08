from z3 import *

def solve_itinerary():
    s = Solver()

    # Days are 1 to 12
    days = 12
    City = Datatype('City')
    City.declare('Dublin')
    City.declare('Riga')
    City.declare('Vilnius')
    City = City.create()

    # Variables for each day's city
    day_city = [Const(f'day_{i}_city', City) for i in range(days)]

    # Variables for flights between days
    flights = [Bool(f'flight_{i}') for i in range(days-1)]

    # Flight constraints
    for i in range(days-1):
        s.add(Implies(flights[i], 
                     Or(And(day_city[i] == City.Dublin, day_city[i+1] == City.Riga),
                        And(day_city[i] == City.Riga, day_city[i+1] == City.Dublin),
                        And(day_city[i] == City.Riga, day_city[i+1] == City.Vilnius),
                        And(day_city[i] == City.Vilnius, day_city[i+1] == City.Riga))))

    # Count days in each city (including flight days)
    dublin_days = Sum([If(day_city[i] == City.Dublin, 1, 0) for i in range(days)])
    riga_days = Sum([If(day_city[i] == City.Riga, 1, 0) for i in range(days)])
    vilnius_days = Sum([If(day_city[i] == City.Vilnius, 1, 0) for i in range(days)])

    # Total flight days (each flight counts for two cities)
    total_flights = Sum([If(flights[i], 1, 0) for i in range(days-1)])

    # City day requirements
    s.add(dublin_days == 2)
    s.add(riga_days == 5)
    s.add(vilnius_days == 7)

    # Total days accounting for overlaps
    s.add(total_flights == 2)  # Since 5+7+2-12=2 overlaps needed

    # Visit all three cities
    s.add(Or([day_city[i] == City.Dublin for i in range(days)]))
    s.add(Or([day_city[i] == City.Riga for i in range(days)]))
    s.add(Or([day_city[i] == City.Vilnius for i in range(days)]))

    # Check for solution
    if s.check() == sat:
        m = s.model()
        itinerary = []
        for i in range(days):
            city = str(m.evaluate(day_city[i]))
            itinerary.append({"day": i+1, "city": city})
        return {"itinerary": itinerary}
    else:
        return {"error": "No valid itinerary found"}

# Execute and print result
import json
print(json.dumps(solve_itinerary(), indent=2))