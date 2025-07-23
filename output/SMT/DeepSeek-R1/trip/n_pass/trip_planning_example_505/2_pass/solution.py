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
    
    # Create Z3 variables: c0 to c8 (9 variables for the end of each day)
    c = [z3.Const('c%d' % i, City) for i in range(9)]
    
    s = z3.Solver()
    
    # Flight constraints for each day transition (from day i-1 to day i, i=1..8)
    for i in range(1, 9):
        c_prev = c[i-1]
        c_curr = c[i]
        # If the city changes, then there must be a direct flight (in either direction)
        conds = []
        for (a, b) in flight_set:
            conds.append(z3.And(c_prev == a, c_curr == b))
            conds.append(z3.And(c_prev == b, c_curr == a))
        flight_ok = z3.Or(conds)
        s.add(z3.If(c_prev == c_curr, True, flight_ok))
    
    # Total days per city: for each city, count the days it appears in the set {c[i-1], c[i]} for i=1..8
    cities_list = [City.Prague, City.Stuttgart, City.Split, City.Krakow, City.Florence]
    total_days = {}
    for city in cities_list:
        total = 0
        for i in range(1, 9):
            total += z3.If(z3.Or(c[i-1] == city, c[i] == city), 1, 0)
        total_days[city] = total
    
    s.add(total_days[City.Prague] == 4)
    s.add(total_days[City.Stuttgart] == 2)
    s.add(total_days[City.Split] == 2)
    s.add(total_days[City.Krakow] == 2)
    s.add(total_days[City.Florence] == 2)
    
    # Event constraints
    # Wedding in Stuttgart between day 2 and 3: must be in Stuttgart on day2 or day3 (or both)
    # Day2: uses c[1] (end of day1) and c[2] (end of day2) -> set {c1, c2}
    # Day3: uses c[2] and c[3] -> set {c2, c3}
    # So: at least one of c1, c2, c3 must be Stuttgart
    s.add(z3.Or(c[1] == City.Stuttgart, c[2] == City.Stuttgart, c[3] == City.Stuttgart))
    
    # Meeting in Split between day3 and day4: must be in Split on day3 or day4 (or both)
    s.add(z3.Or(c[2] == City.Split, c[3] == City.Split, c[4] == City.Split))
    
    # Check and get model
    if s.check() == z3.sat:
        m = s.model()
        itinerary = []
        for day in range(1, 9):
            c_prev_val = m.evaluate(c[day-1])
            c_curr_val = m.evaluate(c[day])
            if c_prev_val.eq(c_curr_val):
                cities = [str(c_prev_val)]
            else:
                cities = sorted([str(c_prev_val), str(c_curr_val)])
            itinerary.append({"day": day, "cities": cities})
        
        result = {"itinerary": itinerary}
        print(json.dumps(result))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()