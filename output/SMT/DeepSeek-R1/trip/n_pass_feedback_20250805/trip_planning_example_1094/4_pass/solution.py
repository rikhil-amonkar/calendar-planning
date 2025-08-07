from z3 import *

def main():
    city_names = ['Vienna', 'Barcelona', 'Edinburgh', 'Krakow', 'Riga', 'Hamburg', 'Paris', 'Stockholm']
    City = Datatype('City')
    for name in city_names:
        City.declare(name)
    City = City.create()
    
    flight_list = [
        ('Hamburg', 'Stockholm'),
        ('Vienna', 'Stockholm'),
        ('Paris', 'Edinburgh'),
        ('Riga', 'Barcelona'),
        ('Paris', 'Riga'),
        ('Krakow', 'Barcelona'),
        ('Edinburgh', 'Stockholm'),
        ('Paris', 'Krakow'),
        ('Krakow', 'Stockholm'),
        ('Riga', 'Edinburgh'),
        ('Barcelona', 'Stockholm'),
        ('Paris', 'Stockholm'),
        ('Krakow', 'Edinburgh'),
        ('Vienna', 'Hamburg'),
        ('Paris', 'Hamburg'),
        ('Riga', 'Stockholm'),
        ('Hamburg', 'Barcelona'),
        ('Vienna', 'Barcelona'),
        ('Krakow', 'Vienna'),
        ('Riga', 'Hamburg'),
        ('Barcelona', 'Edinburgh'),
        ('Paris', 'Barcelona'),
        ('Hamburg', 'Edinburgh'),
        ('Paris', 'Vienna'),
        ('Vienna', 'Riga')
    ]
    
    flight_pairs = []
    for pair in flight_list:
        c1, c2 = pair
        flight_pairs.append((getattr(City, c1), getattr(City, c2)))
    
    c = [None] * 17
    t = [None] * 17
    
    c0 = City.Paris
    
    for i in range(1, 17):
        c[i] = Const(f'c_{i}', City)
        t[i] = Bool(f't_{i}')
    
    s = Solver()
    
    def start_i(i):
        if i == 1:
            return c0
        else:
            return c[i-1]
    
    def in_city(i, city):
        return Or(And(t[i], city == start_i(i)), city == c[i])
    
    # Fixed events: Paris on days 1-2 (no travel, entire day in Paris)
    s.add(Not(t[1]))
    s.add(c[1] == City.Paris)
    s.add(Not(t[2]))
    s.add(c[2] == City.Paris)
    
    # Fixed events: Hamburg on days 10-11 (no travel, entire day in Hamburg)
    s.add(Not(t[10]))
    s.add(c[10] == City.Hamburg)
    s.add(Not(t[11]))
    s.add(c[11] == City.Hamburg)
    
    # Must be in Edinburgh between days 12-15 (inclusive)
    s.add(Or([in_city(i, City.Edinburgh) for i in range(12, 16)]))
    
    # Must be in Stockholm on day 15 or 16
    s.add(Or(in_city(15, City.Stockholm), in_city(16, City.Stockholm)))
    
    # Travel constraints
    for i in range(1, 17):
        s.add(Implies(t[i], start_i(i) != c[i]))
        valid_flight = Or([Or(And(start_i(i) == pair[0], c[i] == pair[1]), And(start_i(i) == pair[1], c[i] == pair[0])) for pair in flight_pairs])
        s.add(Implies(t[i], valid_flight))
    
    # Total days in each city
    total_days = {}
    for city_name in city_names:
        city_const = getattr(City, city_name)
        total = 0
        for i in range(1, 17):
            total += If(in_city(i, city_const), 1, 0)
        total_days[city_const] = total
    
    s.add(total_days[City.Vienna] == 4)
    s.add(total_days[City.Barcelona] == 2)
    s.add(total_days[City.Edinburgh] == 4)
    s.add(total_days[City.Krakow] == 3)
    s.add(total_days[City.Riga] == 4)
    s.add(total_days[City.Hamburg] == 2)
    s.add(total_days[City.Paris] == 2)
    s.add(total_days[City.Stockholm] == 2)
    
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for day in range(1, 17):
            t_val = model.eval(t[day])
            start_val = c0 if day == 1 else model.eval(c[day-1])
            end_val = model.eval(c[day])
            start_name = str(start_val)
            end_name = str(end_val)
            if is_true(t_val):
                cities_day = sorted([start_name, end_name])
            else:
                cities_day = [end_name]
            itinerary.append({"day": day, "cities": cities_day})
        
        import json
        result = {"itinerary": itinerary}
        print(json.dumps(result, indent=2))
    else:
        print("No solution found")

if __name__ == '__main__':
    main()