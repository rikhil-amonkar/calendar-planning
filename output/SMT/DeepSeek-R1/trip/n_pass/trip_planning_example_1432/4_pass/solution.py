from z3 import *
import json

def main():
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
    
    allowed_flights = []
    for a, b in bidirectional_pairs:
        allowed_flights.append((a, b))
        allowed_flights.append((b, a))
    for a, b in directed_pairs:
        allowed_flights.append((a, b))
    
    s = Solver()
    
    CitySort, city_consts = EnumSort('City', cities)
    city_const = {name: city_consts[i] for i, name in enumerate(cities)}
    
    arrival = [Const(f'arrival_{i}', CitySort) for i in range(30)]
    
    for i in range(1, 30):
        current = arrival[i-1]
        next_city = arrival[i]
        s.add(Or(current == next_city, Or([And(current == city_const[a], next_city == city_const[b]) for a, b in allowed_flights])))
    
    for city, days in days_required.items():
        total_days = 0
        c = city_const[city]
        for i in range(1, 30):
            in_city = Or(arrival[i-1] == c, arrival[i] == c)
            total_days += If(in_city, 1, 0)
        s.add(total_days == days)
    
    # Event constraints: each event day must be covered individually
    valencia = city_const['Valencia']
    s.add(Or(arrival[4] == valencia, arrival[5] == valencia))  # Day 5
    s.add(Or(arrival[5] == valencia, arrival[6] == valencia))  # Day 6
    
    riga = city_const['Riga']
    s.add(Or(arrival[17] == riga, arrival[18] == riga))  # Day 18
    s.add(Or(arrival[18] == riga, arrival[19] == riga))  # Day 19
    s.add(Or(arrival[19] == riga, arrival[20] == riga))  # Day 20
    
    athens = city_const['Athens']
    s.add(Or(arrival[13] == athens, arrival[14] == athens))  # Day 14
    s.add(Or(arrival[14] == athens, arrival[15] == athens))  # Day 15
    s.add(Or(arrival[15] == athens, arrival[16] == athens))  # Day 16
    s.add(Or(arrival[16] == athens, arrival[17] == athens))  # Day 17
    
    vienna = city_const['Vienna']
    s.add(Or(arrival[5] == vienna, arrival[6] == vienna))  # Day 6
    s.add(Or(arrival[6] == vienna, arrival[7] == vienna))  # Day 7
    s.add(Or(arrival[7] == vienna, arrival[8] == vienna))  # Day 8
    s.add(Or(arrival[8] == vienna, arrival[9] == vienna))  # Day 9
    s.add(Or(arrival[9] == vienna, arrival[10] == vienna)) # Day 10
    
    stockholm = city_const['Stockholm']
    s.add(Or(arrival[0] == stockholm, arrival[1] == stockholm))  # Day 1
    s.add(Or(arrival[1] == stockholm, arrival[2] == stockholm))  # Day 2
    s.add(Or(arrival[2] == stockholm, arrival[3] == stockholm))  # Day 3
    
    if s.check() == sat:
        model = s.model()
        arr_names = [None] * 30
        for i in range(30):
            for name in cities:
                if model.evaluate(city_const[name]) == model.evaluate(arrival[i]):
                    arr_names[i] = name
                    break
        
        itinerary = []
        if arr_names[0] != arr_names[1]:
            itinerary.append({'day_range': 'Day 1', 'place': arr_names[0]})
        
        current_city = arr_names[1]
        start_day = 1
        for day_index in range(2, 30):
            if arr_names[day_index] != current_city:
                if start_day == day_index - 1:
                    day_range_str = f'Day {start_day}'
                else:
                    day_range_str = f'Day {start_day}-{day_index-1}'
                itinerary.append({'day_range': day_range_str, 'place': current_city})
                current_city = arr_names[day_index]
                start_day = day_index
        
        if start_day == 29:
            day_range_str = 'Day 29'
        else:
            day_range_str = f'Day {start_day}-29'
        itinerary.append({'day_range': day_range_str, 'place': current_city})
        
        result = {'itinerary': itinerary}
        print(json.dumps(result, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()