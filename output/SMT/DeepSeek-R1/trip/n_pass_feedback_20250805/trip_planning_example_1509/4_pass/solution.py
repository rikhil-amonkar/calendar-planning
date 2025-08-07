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
        c1 = I[i]
        c2 = I[i+1]
        s.add(If(c1 == c2, True, (c1, c2) in directed_flights))
    
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
    
    for city in req_days.keys():
        count_assigned = Sum([If(I[i] == city, 1, 0) for i in range(25)])
        travel_starts = Sum([If(And(I[i] == city, I[i+1] != city), 1, 0) for i in range(24)])
        s.add(count_assigned + travel_starts == req_days[city])
        
        first = Int(f'first_{city}')
        last = Int(f'last_{city}')
        s.add(first >= 0)
        s.add(first < 25)
        s.add(last >= 0)
        s.add(last < 25)
        s.add(first <= last)
        s.add(Or([I[i] == city for i in range(25)]))
        for i in range(25):
            s.add(Implies(And(i >= first, i <= last), I[i] == city))
            s.add(Implies(I[i] == city, And(i >= first, i <= last)))
    
    s.add(Or(I[2] == paris, I[3] == paris, I[4] == paris, I[5] == paris, I[6] == paris))
    s.add(Or(I[16] == krakow, I[17] == krakow))
    s.add(Or(I[21] == riga, I[22] == riga))
    s.add(Or(I[10] == santorini, I[11] == santorini))
    s.add(Or(I[16] == helsinki, I[17] == helsinki, I[18] == helsinki, I[19] == helsinki, I[20] == helsinki))
    
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