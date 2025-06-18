from z3 import *

def main():
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
    
    City, city_consts = EnumSort('City', cities_list)
    city_dict = {city: const for city, const in zip(cities_list, city_consts)}
    
    direct_flights_set = set()
    for a, b in given_pairs:
        direct_flights_set.add((city_dict[a], city_dict[b]))
        direct_flights_set.add((city_dict[b], city_dict[a]))
    
    s = Solver()
    
    days = 19
    flight_vars = [Bool(f'flight_{i+1}') for i in range(days)]
    start_city_vars = [Const(f'start_city_{i+1}', City) for i in range(days)]
    end_city_vars = [Const(f'end_city_{i+1}', City) for i in range(days)]
    
    tallinn = city_dict['Tallinn']
    lisbon = city_dict['Lisbon']
    stockholm = city_dict['Stockholm']
    lyon = city_dict['Lyon']
    
    s.add(start_city_vars[0] == tallinn)
    
    for i in range(days):
        flight_day = flight_vars[i]
        start = start_city_vars[i]
        end = end_city_vars[i]
        s.add(If(flight_day, And(start != end, Or([And(start == c1, end == c2) for (c1, c2) in direct_flights_set])), end == start))
        
    for i in range(days - 1):
        s.add(start_city_vars[i+1] == end_city_vars[i])
    
    for city in cities_list:
        total = 0
        city_const = city_dict[city]
        for i in range(days):
            total += If(start_city_vars[i] == city_const, 1, 0)
            total += If(And(flight_vars[i], end_city_vars[i] == city_const), 1, 0)
        s.add(total == required_days[city])
    
    s.add(Sum([If(flight_vars[i], 1, 0) for i in range(days)]) == 7)
    
    event_days_no_flight = [0, 1, 3, 4] + list(range(12, 16)) + [17, 18]
    for day in event_days_no_flight:
        s.add(flight_vars[day] == False)
    
    s.add(start_city_vars[0] == tallinn)
    s.add(start_city_vars[1] == tallinn)
    s.add(end_city_vars[0] == tallinn)
    s.add(end_city_vars[1] == tallinn)
    
    s.add(start_city_vars[3] == lisbon)
    s.add(start_city_vars[4] == lisbon)
    s.add(end_city_vars[3] == lisbon)
    s.add(end_city_vars[4] == lisbon)
    
    for i in range(12, 16):
        s.add(start_city_vars[i] == stockholm)
        s.add(end_city_vars[i] == stockholm)
    
    s.add(start_city_vars[17] == lyon)
    s.add(start_city_vars[18] == lyon)
    s.add(end_city_vars[17] == lyon)
    s.add(end_city_vars[18] == lyon)
    
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