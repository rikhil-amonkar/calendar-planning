from z3 import *

def main():
    # Define city names and create City datatype
    city_names = ['Vienna', 'Barcelona', 'Edinburgh', 'Krakow', 'Riga', 'Hamburg', 'Paris', 'Stockholm']
    City = Datatype('City')
    for name in city_names:
        City.declare(name)
    City = City.create()
    
    # Flight list (bidirectional)
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
    
    # Create flight pairs for Z3 constraints
    flight_pairs = []
    for pair in flight_list:
        c1, c2 = pair
        flight_pairs.append( (getattr(City, c1), getattr(City, c2)) )
    
    # Initialize Z3 variables
    c = [None] * 17  # c[0] is start (Paris), c[1..16] are end cities for days 1..16
    t = [None] * 17  # t[1..16] indicate travel on day i
    
    # c[0] is fixed to Paris
    c0 = City.Paris
    
    # Create Z3 variables for c[1..16] and t[1..16]
    for i in range(1, 17):
        c[i] = Const(f'c_{i}', City)
        t[i] = Bool(f't_{i}')
    
    s = Solver()
    
    # Define helper functions for start_i and in_city
    def start_i(i):
        if i == 1:
            return c0
        else:
            return c[i-1]
    
    def in_city(i, city):
        return Or(And(t[i], city == start_i(i)), city == c[i])
    
    # Fixed day constraints
    s.add(in_city(1, City.Paris))  # Must be in Paris on day 1
    s.add(in_city(2, City.Paris))  # Must be in Paris on day 2
    s.add(in_city(10, City.Hamburg))  # Must be in Hamburg on day 10
    s.add(in_city(11, City.Hamburg))  # Must be in Hamburg on day 11
    
    # Edinburgh meeting constraint (at least one day between 12 and 15)
    s.add(Or([in_city(i, City.Edinburgh) for i in range(12, 16)]))
    
    # Stockholm relatives constraint (at least one day on 15 or 16)
    s.add(Or(in_city(15, City.Stockholm), in_city(16, City.Stockholm))
    
    # Travel constraints: if traveling, must be a direct flight and distinct cities
    for i in range(1, 17):
        s.add(Implies(t[i], start_i(i) != c[i]))
        # Flight constraint: if traveling, the pair (start_i, c[i]) must be in flight_pairs (bidirectional)
        valid_flight = Or([Or(And(start_i(i) == pair[0], c[i] == pair[1]), And(start_i(i) == pair[1], c[i] == pair[0])) for pair in flight_pairs])
        s.add(Implies(t[i], valid_flight))
    
    # Total days per city
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
    
    # Check and get model
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
        
        # Output as JSON dictionary
        import json
        result = {"itinerary": itinerary}
        print(json.dumps(result, indent=2))
    else:
        print("No solution found")

if __name__ == '__main__':
    main()