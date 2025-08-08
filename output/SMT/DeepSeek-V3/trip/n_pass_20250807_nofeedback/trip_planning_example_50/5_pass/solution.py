from z3 import *

def solve_itinerary():
    s = Solver()

    # Define cities and days
    City = Datatype('City')
    City.declare('Vilnius')
    City.declare('Munich')
    City.declare('Mykonos')
    City = City.create()
    Vilnius, Munich, Mykonos = City.Vilnius, City.Munich, City.Mykonos
    days = 12

    # Variables: city for each day
    day_city = [Const(f'day_{i}_city', City) for i in range(days)]

    # Flight constraints
    for i in range(days - 1):
        current = day_city[i]
        next_c = day_city[i + 1]
        s.add(Or(
            current == next_c,  # Stay in same city
            And(current == Vilnius, next_c == Munich),  # V->M
            And(current == Munich, next_c == Vilnius),  # M->V
            And(current == Munich, next_c == Mykonos),  # M->My
            And(current == Mykonos, next_c == Munich)   # My->M
        ))

    # Count days in each city (including flight days)
    def count_days(city):
        return Sum([If(day_city[i] == city, 1, 0) for i in range(days)]) + \
               Sum([If(And(i < days - 1, day_city[i] != city, day_city[i+1] == city), 1, 0) 
                   for i in range(days-1)])

    s.add(count_days(Vilnius) == 4)
    s.add(count_days(Munich) == 3)
    s.add(count_days(Mykonos) == 7)

    # Solve and format output
    if s.check() == sat:
        m = s.model()
        itinerary = []
        for i in range(days):
            day_num = i + 1
            city = m[day_city[i]]
            itinerary.append({"day": day_num, "place": str(city)})
            # If next day is different, current day counts for both
            if i < days - 1 and m[day_city[i]] != m[day_city[i+1]]:
                next_city = m[day_city[i+1]]
                itinerary.append({"day": day_num, "place": str(next_city)})
        return {"itinerary": itinerary}
    else:
        return {"error": "No valid itinerary found"}

result = solve_itinerary()
import json
print(json.dumps(result, indent=2))