from z3 import *
import json

def main():
    # Define the City enumeration
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
    
    # Create directed flight set
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
    
    # Create itinerary variables for 25 days (0-indexed for days 1 to 25)
    I = [Const(f'I_{i}', CitySort) for i in range(25)]
    
    s = Solver()
    
    # Flight constraints for consecutive days
    for i in range(24):
        current_city = I[i]
        next_city = I[i+1]
        flight_options = []
        for (c1, c2) in directed_flights:
            flight_options.append(And(current_city == c1, next_city == c2))
        s.add(If(current_city == next_city, True, Or(flight_options)))
    
    # Function to check presence in a city on a given day
    def present(c, i):
        if i == 0:
            return I[0] == c
        else:
            return Or(I[i-1] == c, I[i] == c)
    
    # Total days constraints per city
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
    
    for city, total_days in req_days.items():
        total_presence = 0
        for i in range(25):
            total_presence += If(present(city, i), 1, 0)
        s.add(total_presence == total_days)
    
    # Event constraints (real day to index: real day d -> index = d-1)
    # Paris: at least one day in [4,8] -> indices [3,7]
    s.add(Or([present(paris, i) for i in range(3, 8)]))
    # Krakow: at least one day in [17,18] -> indices [16,17]
    s.add(Or(present(krakow, 16), present(krakow, 17)))
    # Riga: at least one day in [23,24] -> indices [22,23]
    s.add(Or(present(riga, 22), present(riga, 23)))
    # Santorini: at least one day in [12,13] -> indices [11,12]
    s.add(Or(present(santorini, 11), present(santorini, 12)))
    # Helsinki: at least one day in [18,22] -> indices [17,21]
    s.add(Or([present(helsinki, i) for i in range(17, 22)]))
    
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