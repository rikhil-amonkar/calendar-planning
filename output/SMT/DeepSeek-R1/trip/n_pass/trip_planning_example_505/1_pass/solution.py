import z3
import json

def main():
    # Define the City enum
    City = z3.Datatype('City')
    City.declare('Prague')
    City.declare('Stuttgart')
    City.declare('Split')
    City.declare('Krakow')
    City.declare('Florence')
    City = City.create()
    
    # Define direct flights (as tuples of City constants)
    flight_set = [
        (City.Stuttgart, City.Split),
        (City.Prague, City.Florence),
        (City.Krakow, City.Stuttgart),
        (City.Krakow, City.Split),
        (City.Split, City.Prague),
        (City.Krakow, City.Prague)
    ]
    
    # Create symmetric flight set (both directions)
    sym_flight_set = set()
    for (a, b) in flight_set:
        sym_flight_set.add((a, b))
        sym_flight_set.add((b, a))
    
    # Create Z3 variables: current_city[0..8] and fly[1..8]
    current_city = [z3.Const('current_city_%d' % i, City) for i in range(9)]
    fly = [z3.Bool('fly_%d' % i) for i in range(1, 9)]
    
    s = z3.Solver()
    
    # Flight constraints for each day 1..8
    for i in range(1, 9):
        # If flying, the flight must be in sym_flight_set
        flight_cond = z3.Or([z3.And(current_city[i-1] == a, current_city[i] == b) for (a, b) in sym_flight_set])
        s.add(z3.If(fly[i-1], flight_cond, current_city[i] == current_city[i-1]))
    
    # Total days per city
    total_days = {}
    cities_list = [City.Prague, City.Stuttgart, City.Split, City.Krakow, City.Florence]
    for c in cities_list:
        total = 0
        for i in range(1, 9):
            in_city = z3.Or(current_city[i-1] == c, current_city[i] == c)
            total += z3.If(in_city, 1, 0)
        total_days[c] = total
    
    s.add(total_days[City.Prague] == 4)
    s.add(total_days[City.Stuttgart] == 2)
    s.add(total_days[City.Split] == 2)
    s.add(total_days[City.Krakow] == 2)
    s.add(total_days[City.Florence] == 2)
    
    # Event constraints
    st_day2 = z3.Or(current_city[1] == City.Stuttgart, current_city[2] == City.Stuttgart)
    st_day3 = z3.Or(current_city[2] == City.Stuttgart, current_city[3] == City.Stuttgart)
    s.add(z3.Or(st_day2, st_day3))
    
    sp_day3 = z3.Or(current_city[2] == City.Split, current_city[3] == City.Split)
    sp_day4 = z3.Or(current_city[3] == City.Split, current_city[4] == City.Split)
    s.add(z3.Or(sp_day3, sp_day4))
    
    # Check and get model
    if s.check() == z3.sat:
        m = s.model()
        itinerary = []
        for d in range(1, 9):
            c0_val = m.evaluate(current_city[d-1])
            c1_val = m.evaluate(current_city[d])
            c0_str = str(c0_val)
            c1_str = str(c1_val)
            cities_on_day = set()
            cities_on_day.add(c0_str)
            cities_on_day.add(c1_str)
            sorted_cities = sorted(list(cities_on_day))
            itinerary.append({"day": d, "cities": sorted_cities})
        
        result = {"itinerary": itinerary}
        print(json.dumps(result))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()