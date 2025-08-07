from z3 import *
import json

def main():
    # Define the cities and their required stay durations
    cities = ['Frankfurt', 'Salzburg', 'Athens', 'Reykjavik', 'Bucharest', 'Valencia', 'Vienna', 'Amsterdam', 'Stockholm', 'Riga']
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
    
    # Define the allowed flights (bidirectional and directed)
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
    allowed_flights = []
    for a, b in bidirectional_pairs:
        allowed_flights.append((a, b))
        allowed_flights.append((b, a))
    for a, b in directed_pairs:
        allowed_flights.append((a, b))
    
    # Create Z3 solver
    s = Solver()
    
    # Define city enum sort
    CitySort, city_consts = EnumSort('City', cities)
    city_const = {name: city_consts[i] for i, name in enumerate(cities)}
    
    # Create arrival variables for 30 time points (start day1 to end day29)
    arrival = [Const(f'arrival_{i}', CitySort) for i in range(30)]
    
    # Flight constraints: for each day transition, either stay or take an allowed flight
    for i in range(1, 30):
        current_city = arrival[i-1]
        next_city = arrival[i]
        stay = current_city == next_city
        flight_options = []
        for a, b in allowed_flights:
            a_const = city_const[a]
            b_const = city_const[b]
            flight_options.append(And(current_city == a_const, next_city == b_const))
        s.add(Or(stay, Or(flight_options)))
    
    # Stay duration constraints: for each city, count the days it appears (either start or end of day)
    for city, days in days_required.items():
        total_days = 0
        c_const = city_const[city]
        for day in range(1, 30):  # day1 to day29
            # Day 'day' is from time day-1 to time day
            in_city = Or(arrival[day-1] == c_const, arrival[day] == c_const)
            total_days += If(in_city, 1, 0)
        s.add(total_days == days)
    
    # Event constraints
    # Valencia: must be present on day5 and day6
    s.add(Or(arrival[4] == city_const['Valencia'], arrival[5] == city_const['Valencia']))  # day5
    s.add(Or(arrival[5] == city_const['Valencia'], arrival[6] == city_const['Valencia']))  # day6
    
    # Riga: must be present on day18,19,20
    s.add(Or(arrival[17] == city_const['Riga'], arrival[18] == city_const['Riga']))  # day18
    s.add(Or(arrival[18] == city_const['Riga'], arrival[19] == city_const['Riga']))  # day19
    s.add(Or(arrival[19] == city_const['Riga'], arrival[20] == city_const['Riga']))  # day20
    
    # Athens: must be present on at least one day between 14 and 18 (inclusive)
    athens_days = []
    for d in range(14, 19):  # days 14 to 18
        athens_days.append(Or(arrival[d-1] == city_const['Athens'], arrival[d] == city_const['Athens']))
    s.add(Or(athens_days))
    
    # Vienna: must be present on at least one day between 6 and 10 (inclusive)
    vienna_days = []
    for d in range(6, 11):  # days 6 to 10
        vienna_days.append(Or(arrival[d-1] == city_const['Vienna'], arrival[d] == city_const['Vienna']))
    s.add(Or(vienna_days))
    
    # Stockholm: must be present on at least one day between 1 and 3 (inclusive)
    stockholm_days = []
    for d in range(1, 4):  # days 1 to 3
        stockholm_days.append(Or(arrival[d-1] == city_const['Stockholm'], arrival[d] == city_const['Stockholm']))
    s.add(Or(stockholm_days))
    
    # Solve the constraints
    if s.check() == sat:
        model = s.model()
        # Map model values to city names
        arr_names = []
        for i in range(30):
            c_val = model.eval(arrival[i])
            for name in cities:
                if model.eval(city_const[name]) == c_val:
                    arr_names.append(name)
                    break
        
        # Build itinerary for each day (1 to 29)
        itinerary = []
        for day in range(1, 30):
            start_city = arr_names[day-1]
            end_city = arr_names[day]
            if start_city == end_city:
                places = [start_city]
            else:
                places = sorted([start_city, end_city])
            itinerary.append({"day": day, "place": places})
        
        # Output as JSON
        result = {"itinerary": itinerary}
        print(json.dumps(result, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()