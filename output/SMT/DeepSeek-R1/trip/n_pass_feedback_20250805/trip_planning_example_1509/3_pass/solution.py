from z3 import *
import json

def main():
    CitySort, (paris, warsaw, krakow, tallinn, riga, copenhagen, helsinki, oslo, santorini, lyon) = EnumSort('City', [
        'Paris', 'Warsaw', 'Krakow', 'Tallinn', 'Riga', 'Copenhagen', 'Helsinki', 'Oslo', 'Santorini', 'Lyon'
    ])
    
    cities = ['Paris', 'Warsaw', 'Krakow', 'Tallinn', 'Riga', 'Copenhagen', 'Helsinki', 'Oslo', 'Santorini', 'Lyon']
    city_dict = {
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
    
    flight_list_text = [
        "Warsaw and Riga",
        "Warsaw and Tallinn",
        "Copenhagen and Helsinki",
        "Lyon and Paris",
        "Copenhagen and Warsaw",
        "Lyon and Oslo",
        "Paris and Oslo",
        "Paris and Riga",
        "Krakow and Helsinki",
        "Paris and Tallinn",
        "Oslo and Riga",
        "Krakow and Warsaw",
        "Paris and Helsinki",
        "Copenhagen and Santorini",
        "Helsinki and Warsaw",
        "Helsinki and Riga",
        "Copenhagen and Krakow",
        "Copenhagen and Riga",
        "Paris and Krakow",
        "Copenhagen and Oslo",
        "Oslo and Tallinn",
        "Oslo and Helsinki",
        "Copenhagen and Tallinn",
        "Oslo and Krakow",
        "from Riga to Tallinn",
        "Helsinki and Tallinn",
        "Paris and Copenhagen",
        "Paris and Warsaw",
        "from Santorini to Oslo",
        "Oslo and Warsaw"
    ]
    
    directed_flights = set()
    for item in flight_list_text:
        if item.startswith("from"):
            parts = item.split()
            from_city = parts[1]
            to_city = parts[3]
            directed_flights.add((city_dict[from_city], city_dict[to_city]))
        else:
            parts = item.split(' and ')
            c1 = parts[0].strip()
            c2 = parts[1].strip()
            directed_flights.add((city_dict[c1], city_dict[c2]))
            directed_flights.add((city_dict[c2], city_dict[c1]))
    
    I = [Const(f'I_{i}', CitySort) for i in range(25)]
    s = Solver()
    
    for i in range(24):
        current_city = I[i]
        next_city = I[i+1]
        flight_options = []
        for (c1, c2) in directed_flights:
            flight_options.append(And(current_city == c1, next_city == c2))
        s.add(If(current_city == next_city, True, Or(flight_options)))
    
    def is_present(c, i):
        conditions = [I[i] == c]
        if i < 24:
            conditions.append(And(I[i] != c, I[i+1] == c))
        if i > 0:
            conditions.append(And(I[i-1] == c, I[i] != c))
        return Or(conditions)
    
    req_days = {
        paris: 5,
        warsaw: 2,
        krakow: 2,
        tallinn: 2,
        riga: 2,
        copenhagen: 5,
        helsinki: 5,
        oslo: 5,
        santorini: 2,
        lyon: 4
    }
    
    for city, total in req_days.items():
        total_presence = 0
        for i in range(25):
            total_presence += If(is_present(city, i), 1, 0)
        s.add(total_presence == total)
    
    s.add(Or([is_present(paris, i) for i in [3,4,5,6,7]]))
    s.add(Or(is_present(krakow, 16), is_present(krakow, 17)))
    s.add(Or(is_present(riga, 22), is_present(riga, 23)))
    s.add(Or(is_present(santorini, 11), is_present(santorini, 12)))
    s.add(Or([is_present(helsinki, i) for i in [17,18,19,20,21]]))
    
    for city in [paris, warsaw, krakow, tallinn, riga, copenhagen, helsinki, oslo, santorini, lyon]:
        for i in range(1, 25):
            if i-1 > 0:
                for j in range(0, i-1):
                    s.add(Implies(And(Not(is_present(city, i-1)), is_present(city, i)), Not(is_present(city, j))))
        for i in range(0, 24):
            if i+2 < 25:
                for j in range(i+2, 25):
                    s.add(Implies(And(is_present(city, i), Not(is_present(city, i+1))), Not(is_present(city, j))))
    
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