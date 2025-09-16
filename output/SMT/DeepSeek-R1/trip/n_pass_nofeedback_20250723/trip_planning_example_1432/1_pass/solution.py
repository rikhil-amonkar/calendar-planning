from z3 import *
import json

def main():
    # Define the cities
    cities = ['Frankfurt', 'Salzburg', 'Athens', 'Reykjavik', 'Bucharest', 'Valencia', 'Vienna', 'Amsterdam', 'Stockholm', 'Riga']
    
    # Required days per city
    days_required = {
        'Frankfurt': 4,
        'Salzburg': 5,
        'Athens': 5,
        'Reykjavik': 5,
        'Bucharest': 3,
        'Valencia': 2,
        'Vienna': 5,
        'Amsterdam': 3,
        'Stockholm': 3,
        'Riga': 3
    }
    
    # Define the direct flights
    bidirectional_pairs = [
        ('Valencia', 'Frankfurt'),
        ('Vienna', 'Bucharest'),
        ('Athens', 'Bucharest'),
        ('Riga', 'Frankfurt'),
        ('Stockholm', 'Athens'),
        ('Amsterdam', 'Bucharest'),
        ('Amsterdam', 'Frankfurt'),
        ('Stockholm', 'Vienna'),
        ('Vienna', 'Riga'),
        ('Amsterdam', 'Reykjavik'),
        ('Reykjavik', 'Frankfurt'),
        ('Stockholm', 'Amsterdam'),
        ('Amsterdam', 'Valencia'),
        ('Vienna', 'Frankfurt'),
        ('Valencia', 'Bucharest'),
        ('Bucharest', 'Frankfurt'),
        ('Stockholm', 'Frankfurt'),
        ('Valencia', 'Vienna'),
        ('Frankfurt', 'Salzburg'),
        ('Amsterdam', 'Vienna'),
        ('Stockholm', 'Reykjavik'),
        ('Amsterdam', 'Riga'),
        ('Stockholm', 'Riga'),
        ('Vienna', 'Reykjavik'),
        ('Amsterdam', 'Athens'),
        ('Athens', 'Frankfurt'),
        ('Vienna', 'Athens'),
        ('Riga', 'Bucharest')
    ]
    
    directed_pairs = [
        ('Valencia', 'Athens'),
        ('Athens', 'Riga'),
        ('Reykjavik', 'Athens')
    ]
    
    # Create the list of allowed flights (both directions for bidirectional and one direction for directed)
    allowed_list = []
    for (a, b) in bidirectional_pairs:
        allowed_list.append((a, b))
        allowed_list.append((b, a))
    for (a, b) in directed_pairs:
        allowed_list.append((a, b))
    
    # Create the Z3 solver
    s = Solver()
    
    # Define the city enum sort
    CitySort, city_consts = EnumSort('City', cities)
    city_const = {name: city_consts[i] for i, name in enumerate(cities)}
    
    # Create arrival variables: 30 time points (start at day1 time0 to end of day29 time29)
    arrival = [Const('arrival_%d' % i, CitySort) for i in range(30)]
    
    # Flight constraints for each transition (from time i-1 to time i, for i in 1..29)
    for i in range(1, 30):
        # Either stay in the same city or take an allowed flight
        stay = (arrival[i-1] == arrival[i])
        # Flight: one of the allowed_list flights
        flight_options = []
        for (a_str, b_str) in allowed_list:
            a_const = city_const[a_str]
            b_const = city_const[b_str]
            flight_options.append(And(arrival[i-1] == a_const, arrival[i] == b_const))
        s.add(Or(stay, Or(flight_options)))
    
    # Total days per city constraint
    for city_name in cities:
        total_days = 0
        for day in range(1, 30):  # day from 1 to 29
            # The set for day 'day' is determined by arrival[day-1] and arrival[day]
            in_city = Or(arrival[day-1] == city_const[city_name], arrival[day] == city_const[city_name])
            total_days += If(in_city, 1, 0)
        s.add(total_days == days_required[city_name])
    
    # Event constraints
    # Valencia: must be in Valencia on day5 and day6
    day5_valencia = Or(arrival[4] == city_const['Valencia'], arrival[5] == city_const['Valencia'])
    day6_valencia = Or(arrival[5] == city_const['Valencia'], arrival[6] == city_const['Valencia'])
    s.add(day5_valencia, day6_valencia)
    
    # Riga: must be in Riga on day18,19,20
    for d in [18,19,20]:
        in_riga = Or(arrival[d-1] == city_const['Riga'], arrival[d] == city_const['Riga'])
        s.add(in_riga)
    
    # Athens: must be in Athens on at least one day between 14 and 18 (inclusive)
    athens_days = []
    for d in range(14,19):  # days 14 to 18 inclusive
        in_athens = Or(arrival[d-1] == city_const['Athens'], arrival[d] == city_const['Athens'])
        athens_days.append(in_athens)
    s.add(Or(athens_days))
    
    # Vienna: must be in Vienna on at least one day between 6 and 10 (inclusive)
    vienna_days = []
    for d in range(6,11):  # days 6 to 10 inclusive
        in_vienna = Or(arrival[d-1] == city_const['Vienna'], arrival[d] == city_const['Vienna'])
        vienna_days.append(in_vienna)
    s.add(Or(vienna_days))
    
    # Stockholm: must be in Stockholm on at least one day between 1 and 3 (inclusive)
    stockholm_days = []
    for d in range(1,4):  # days 1 to 3 inclusive
        in_stockholm = Or(arrival[d-1] == city_const['Stockholm'], arrival[d] == city_const['Stockholm'])
        stockholm_days.append(in_stockholm)
    s.add(Or(stockholm_days))
    
    # Check for a solution
    if s.check() == sat:
        model = s.model()
        # Map the model values to city names
        arr_names = []
        for i in range(30):
            c_val = model.eval(arrival[i])
            for name in cities:
                if model.eval(city_const[name]) == c_val:
                    arr_names.append(name)
                    break
        
        # Build the itinerary for each day (day1 to day29)
        itinerary = []
        for day in range(1, 30):
            city0 = arr_names[day-1]   # at time (day-1)
            city1 = arr_names[day]      # at time (day)
            if city0 == city1:
                places = [city0]
            else:
                places = sorted([city0, city1])
            itinerary.append({"day": day, "place": places})
        
        # Output as JSON
        result = {'itinerary': itinerary}
        print(json.dumps(result, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()