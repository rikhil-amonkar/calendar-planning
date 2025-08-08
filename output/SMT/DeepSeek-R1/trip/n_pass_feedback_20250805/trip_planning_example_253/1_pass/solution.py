from z3 import *
import json

def main():
    # Define the City enumeration
    City = Datatype('City')
    City.declare('Amsterdam')
    City.declare('Vienna')
    City.declare('Santorini')
    City.declare('Lyon')
    City = City.create()
    
    # Define direct flight pairs (both directions)
    edges = [
        (City.Vienna, City.Lyon),
        (City.Vienna, City.Santorini),
        (City.Vienna, City.Amsterdam),
        (City.Amsterdam, City.Santorini),
        (City.Lyon, City.Amsterdam)
    ]
    direct_pairs = []
    for (a, b) in edges:
        direct_pairs.append((a, b))
        direct_pairs.append((b, a))
    
    # Create Z3 solver
    s = Solver()
    
    # Arrays for beginning and end cities for each day (1 to 14)
    b = [None]  # index 0 unused
    e = [None]  # index 0 unused
    for i in range(1, 15):
        b.append(Const(f'b_{i}', City))
        e.append(Const(f'e_{i}', City))
    
    # Constraint: For i from 2 to 14, b[i] = e[i-1]
    for i in range(2, 15):
        s.add(b[i] == e[i-1])
    
    # Constraint: If b[i] != e[i], then there must be a direct flight
    for i in range(1, 15):
        constraint = Or([And(b[i] == c1, e[i] == c2) for (c1, c2) in direct_pairs])
        s.add(If(b[i] != e[i], constraint, True))
    
    # Total days per city
    total_days = { 
        City.Amsterdam: 0,
        City.Vienna: 0,
        City.Santorini: 0,
        City.Lyon: 0
    }
    for city in total_days.keys():
        for i in range(1, 15):
            total_days[city] += If(Or(b[i] == city, e[i] == city), 1, 0)
    
    s.add(total_days[City.Amsterdam] == 3)
    s.add(total_days[City.Vienna] == 7)
    s.add(total_days[City.Santorini] == 4)
    s.add(total_days[City.Lyon] == 3)
    
    # Workshop constraint: Amsterdam between days 9-11
    workshop_days = []
    for i in [9, 10, 11]:
        workshop_days.append(Or(b[i] == City.Amsterdam, e[i] == City.Amsterdam))
    s.add(Or(workshop_days))
    
    # Wedding constraint: Lyon between days 7-9
    wedding_days = []
    for i in [7, 8, 9]:
        wedding_days.append(Or(b[i] == City.Lyon, e[i] == City.Lyon))
    s.add(Or(wedding_days))
    
    # Travel days constraint: exactly 3 travel days
    travel_days = [If(b[i] != e[i], 1, 0) for i in range(1, 15)]
    s.add(sum(travel_days) == 3)
    
    # Check and get model
    if s.check() == sat:
        m = s.model()
        itinerary_list = []
        for i in range(1, 15):
            city_val = m[e[i]]
            if is_as_int(city_val):
                city_int = city_val.as_long()
                if city_int == City.Amsterdam.index():
                    place = "Amsterdam"
                elif city_int == City.Vienna.index():
                    place = "Vienna"
                elif city_int == City.Santorini.index():
                    place = "Santorini"
                elif city_int == City.Lyon.index():
                    place = "Lyon"
                else:
                    place = "Unknown"
                itinerary_list.append({"day": i, "place": place})
        
        result = {"itinerary": itinerary_list}
        print(json.dumps(result))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()