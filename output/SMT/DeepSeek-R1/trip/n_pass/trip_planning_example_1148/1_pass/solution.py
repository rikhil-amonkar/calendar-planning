from z3 import *

def main():
    # Cities and their required days
    cities_list = ['Lisbon', 'Dubrovnik', 'Copenhagen', 'Prague', 'Tallinn', 'Stockholm', 'Split', 'Lyon']
    required_days = {
        'Lisbon': 2,
        'Dubrovnik': 5,
        'Copenhagen': 5,
        'Prague': 3,
        'Tallinn': 2,
        'Stockholm': 4,
        'Split': 3,
        'Lyon': 2
    }
    
    # Direct flight pairs (both directions)
    given_pairs = [
        ('Dubrovnik', 'Stockholm'),
        ('Lisbon', 'Copenhagen'),
        ('Lisbon', 'Lyon'),
        ('Copenhagen', 'Stockholm'),
        ('Copenhagen', 'Split'),
        ('Prague', 'Stockholm'),
        ('Tallinn', 'Stockholm'),
        ('Prague', 'Lyon'),
        ('Lisbon', 'Stockholm'),
        ('Prague', 'Lisbon'),
        ('Stockholm', 'Split'),
        ('Prague', 'Split'),
        ('Split', 'Lyon'),
        ('Copenhagen', 'Dubrovnik'),
        ('Tallinn', 'Copenhagen'),
        ('Tallinn', 'Prague')
    ]
    
    # Create Z3 enums for cities
    City, city_consts = EnumSort('City', cities_list)
    city_dict = {city: const for city, const in zip(cities_list, city_consts)}
    
    # Build directed flight set (both directions)
    direct_flights_const = set()
    for a, b in given_pairs:
        direct_flights_const.add((city_dict[a], city_dict[b]))
        direct_flights_const.add((city_dict[b], city_dict[a]))
    
    # Initialize solver
    s = Solver()
    
    # Variables for each day (1 to 19)
    days = 19
    flight_vars = [Bool(f'flight_{i+1}') for i in range(days)]
    start_city_vars = [Const(f'start_city_{i+1}', City) for i in range(days)]
    end_city_vars = [Const(f'end_city_{i+1}', City) for i in range(days)]
    
    # Flight and city constraints per day
    for i in range(days):
        flight_day = flight_vars[i]
        start = start_city_vars[i]
        end = end_city_vars[i]
        
        # If flying, ensure direct flight and different cities
        flight_cond = Or([And(start == c1, end == c2) for (c1, c2) in direct_flights_const])
        s.add(If(flight_day, And(start != end, flight_cond), end == start))
    
    # Continuity between days
    for i in range(days - 1):
        s.add(start_city_vars[i+1] == end_city_vars[i])
    
    # Total days per city
    for city in cities_list:
        total = 0
        city_const = city_dict[city]
        for i in range(days):
            total += If(start_city_vars[i] == city_const, 1, 0)
            total += If(And(flight_vars[i], end_city_vars[i] == city_const), 1, 0)
        s.add(total == required_days[city])
    
    # Total flight days must be 7
    s.add(Sum([If(flight_vars[i], 1, 0) for i in range(days)]) == 7)
    
    # Event constraints
    lyon = city_dict['Lyon']
    s.add(Or(start_city_vars[17] == lyon, And(flight_vars[17], end_city_vars[17] == lyon)))  # Day 18
    s.add(Or(start_city_vars[18] == lyon, And(flight_vars[18], end_city_vars[18] == lyon)))  # Day 19
    
    tallinn = city_dict['Tallinn']
    s.add(Or(
        Or(start_city_vars[0] == tallinn, And(flight_vars[0], end_city_vars[0] == tallinn)),
        Or(start_city_vars[1] == tallinn, And(flight_vars[1], end_city_vars[1] == tallinn))
    ))  # Day 1 or 2
    
    lisbon = city_dict['Lisbon']
    s.add(Or(
        Or(start_city_vars[3] == lisbon, And(flight_vars[3], end_city_vars[3] == lisbon)),
        Or(start_city_vars[4] == lisbon, And(flight_vars[4], end_city_vars[4] == lisbon))
    ))  # Day 4 or 5
    
    stockholm = city_dict['Stockholm']
    stockholm_days = [12, 13, 14, 15]  # Days 13 to 16 (0-indexed)
    s.add(Or([Or(start_city_vars[d] == stockholm, And(flight_vars[d], end_city_vars[d] == stockholm)) for d in stockholm_days]))
    
    # Solve and output
    if s.check() == sat:
        m = s.model()
        rev_city_dict = {const: name for name, const in city_dict.items()}
        
        for i in range(days):
            day = i + 1
            start_val = m.eval(start_city_vars[i])
            flight_val = m.eval(flight_vars[i])
            end_val = m.eval(end_city_vars[i])
            start_name = rev_city_dict[start_val]
            end_name = rev_city_dict[end_val]
            
            if is_true(flight_val):
                print(f"Day {day}: Start in {start_name}, fly to {end_name}")
            else:
                print(f"Day {day}: Stay in {start_name}")
    else:
        print("No solution found")

if __name__ == '__main__':
    main()