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
    
    # Event constraints
    valencia = city_const['Valencia']
    s.add(Or(arrival[4] == valencia, arrival[5] == valencia))
    s.add(Or(arrival[5] == valencia, arrival[6] == valencia))
    
    riga = city_const['Riga']
    s.add(Or(arrival[17] == riga, arrival[18] == riga))
    s.add(Or(arrival[18] == riga, arrival[19] == riga))
    s.add(Or(arrival[19] == riga, arrival[20] == riga))
    
    athens = city_const['Athens']
    athens_days = []
    for d in range(14, 19):
        athens_days.append(Or(arrival[d-1] == athens, arrival[d] == athens))
    s.add(Or(athens_days))
    
    vienna = city_const['Vienna']
    vienna_days = []
    for d in range(6, 11):
        vienna_days.append(Or(arrival[d-1] == vienna, arrival[d] == vienna))
    s.add(Or(vienna_days))
    
    stockholm = city_const['Stockholm']
    stockholm_days = []
    for d in range(1, 4):
        stockholm_days.append(Or(arrival[d-1] == stockholm, arrival[d] == stockholm))
    s.add(Or(stockholm_days))
    
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
            itinerary.append({'day_range': f'Day 1', 'place': arr_names[0]})
        
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