from z3 import *
import json

def main():
    # Define the City enumeration
    CitySort, (paris, warsaw, krakow, tallinn, riga, copenhagen, helsinki, oslo, santorini, lyon) = EnumSort('City', [
        'Paris', 'Warsaw', 'Krakow', 'Tallinn', 'Riga', 'Copenhagen', 'Helsinki', 'Oslo', 'Santorini', 'Lyon'
    ])
    
    cities = ['Paris', 'Warsaw', 'Krakow', 'Tallinn', 'Riga', 'Copenhagen', 'Helsinki', 'Oslo', 'Santorini', 'Lyon']
    city_vars = {
        'Paris': paris,
        'Warsaw': warsaw,
        'Krakow': krakow,
        'Tallinn': tallinn,
        'Riga': riga,
        'Copenhagen': copenhagen,
        'Helsinki': helsinki,
        'Oslo': oslo,
        'Santorini': santorini,
        'Lyon': lyon
    }
    
    # Create itinerary variables for 25 days
    I = [Const(f'I_{i}', CitySort) for i in range(25)]
    
    # Flight connections (bidirectional)
    flight_pairs = [
        ('Warsaw', 'Riga'),
        ('Warsaw', 'Tallinn'),
        ('Copenhagen', 'Helsinki'),
        ('Lyon', 'Paris'),
        ('Copenhagen', 'Warsaw'),
        ('Lyon', 'Oslo'),
        ('Paris', 'Oslo'),
        ('Paris', 'Riga'),
        ('Krakow', 'Helsinki'),
        ('Paris', 'Tallinn'),
        ('Oslo', 'Riga'),
        ('Krakow', 'Warsaw'),
        ('Paris', 'Helsinki'),
        ('Copenhagen', 'Santorini'),
        ('Helsinki', 'Warsaw'),
        ('Helsinki', 'Riga'),
        ('Copenhagen', 'Krakow'),
        ('Copenhagen', 'Riga'),
        ('Paris', 'Krakow'),
        ('Copenhagen', 'Oslo'),
        ('Oslo', 'Tallinn'),
        ('Oslo', 'Helsinki'),
        ('Copenhagen', 'Tallinn'),
        ('Oslo', 'Krakow'),
        ('Riga', 'Tallinn'),
        ('Helsinki', 'Tallinn'),
        ('Paris', 'Copenhagen'),
        ('Paris', 'Warsaw'),
        ('Santorini', 'Oslo'),
        ('Oslo', 'Warsaw')
    ]
    
    flight_set = set()
    for a, b in flight_pairs:
        flight_set.add((city_vars[a], city_vars[b]))
        flight_set.add((city_vars[b], city_vars[a]))
    
    s = Solver()
    
    # Flight constraints for consecutive days
    for i in range(24):
        current_city = I[i]
        next_city = I[i+1]
        s.add(If(current_city != next_city,
                 Or([And(current_city == c1, next_city == c2) for (c1, c2) in flight_set]),
                 True))
    
    # Function to check presence in a city on a given day
    def present(c, day_index):
        if day_index == 0:
            return I[0] == c
        elif day_index == 24:
            return I[24] == c
        else:
            return Or(
                I[day_index] == c,
                And(I[day_index-1] == c, I[day_index] != c),
                And(I[day_index+1] == c, I[day_index] != c)
            )
    
    # Event constraints
    s.add(present(city_vars['Krakow'], 16))  # Day 17
    s.add(present(city_vars['Krakow'], 17))  # Day 18
    s.add(present(city_vars['Riga'], 22))    # Day 23
    s.add(present(city_vars['Riga'], 23))    # Day 24
    s.add(present(city_vars['Santorini'], 11))  # Day 12
    s.add(present(city_vars['Santorini'], 12))  # Day 13
    s.add(Or([present(city_vars['Paris'], d) for d in [3, 4, 5, 6, 7]]))  # Days 4-8
    s.add(Or([present(city_vars['Helsinki'], d) for d in range(17, 22)]))  # Days 18-22
    
    # Total days constraints per city
    req_days = {
        'Paris': 5,
        'Warsaw': 2,
        'Krakow': 2,
        'Tallinn': 2,
        'Riga': 2,
        'Copenhagen': 5,
        'Helsinki': 5,
        'Oslo': 5,
        'Santorini': 2,
        'Lyon': 4
    }
    
    for city, total_days in req_days.items():
        c = city_vars[city]
        total = 0
        for d in range(25):
            total += If(present(c, d), 1, 0)
        s.add(total == total_days)
    
    # Solve the problem
    if s.check() == sat:
        m = s.model()
        city_names = {
            paris: 'Paris',
            warsaw: 'Warsaw',
            krakow: 'Krakow',
            tallinn: 'Tallinn',
            riga: 'Riga',
            copenhagen: 'Copenhagen',
            helsinki: 'Helsinki',
            oslo: 'Oslo',
            santorini: 'Santorini',
            lyon: 'Lyon'
        }
        itinerary = []
        for i in range(25):
            city_sym = m[I[i]]
            city_name = city_names[city_sym]
            itinerary.append({'day': i+1, 'place': city_name})
        
        result = {'itinerary': itinerary}
        print(json.dumps(result))
    else:
        print("No solution found")

if __name__ == '__main__':
    main()