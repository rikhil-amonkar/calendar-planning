from z3 import *
import json

def main():
    # Define cities and allowed flights
    cities = ["Vienna", "Milan", "Rome", "Riga", "Lisbon", "Vilnius", "Oslo"]
    City, (Vienna, Milan, Rome, Riga, Lisbon, Vilnius, Oslo) = EnumSort('City', cities)
    city_map = {name: const for name, const in zip(cities, [Vienna, Milan, Rome, Riga, Lisbon, Vilnius, Oslo])}
    
    # Allowed flights (bidirectional and directed)
    bidirectional_connections = [
        ("Riga", "Oslo"),
        ("Vienna", "Milan"),
        ("Vienna", "Vilnius"),
        ("Vienna", "Lisbon"),
        ("Riga", "Milan"),
        ("Lisbon", "Oslo"),
        ("Rome", "Lisbon"),
        ("Vienna", "Riga"),
        ("Vienna", "Rome"),
        ("Milan", "Oslo"),
        ("Vienna", "Oslo"),
        ("Vilnius", "Oslo"),
        ("Vilnius", "Milan"),
        ("Riga", "Lisbon"),
        ("Milan", "Lisbon"),
        ("Rome", "Oslo")
    ]
    directed_connections = [
        ("Rome", "Riga"),
        ("Riga", "Vilnius")
    ]
    allowed_flights = set()
    for a, b in bidirectional_connections:
        allowed_flights.add((a, b))
        allowed_flights.add((b, a))
    for a, b in directed_connections:
        allowed_flights.add((a, b))
    
    # Create Z3 solver and itinerary variables
    n_days = 15
    itinerary = [Const(f'itinerary_{i}', City) for i in range(n_days)]
    s = Solver()
    
    # Day 1 must be Vienna
    s.add(itinerary[0] == Vienna)
    
    # Define presence in city for each day
    def in_city(city, day):
        if day == 0:
            return itinerary[0] == city
        else:
            return Or(
                itinerary[day] == city,
                And(itinerary[day-1] == city, itinerary[day] != city)
            )
    
    # Total days per city constraints
    total_days = {city: 0 for city in [Vienna, Milan, Rome, Riga, Lisbon, Vilnius, Oslo]}
    for city in total_days:
        total_days[city] = Sum([If(in_city(city, d), 1, 0) for d in range(n_days)])
    s.add(total_days[Vienna] == 4)
    s.add(total_days[Milan] == 2)
    s.add(total_days[Rome] == 3)
    s.add(total_days[Riga] == 2)
    s.add(total_days[Lisbon] == 3)
    s.add(total_days[Vilnius] == 4)
    s.add(total_days[Oslo] == 3)
    
    # Fixed events
    s.add(in_city(Vienna, 3))  # Day 4 must include Vienna
    s.add(Or(in_city(Lisbon, 10), in_city(Lisbon, 11), in_city(Lisbon, 12)))  # Lisbon between days 11-13
    s.add(Or(in_city(Oslo, 12), in_city(Oslo, 13), in_city(Oslo, 14)))  # Oslo between days 13-15
    
    # Flight constraints
    for day in range(1, n_days):
        from_city = itinerary[day-1]
        to_city = itinerary[day]
        flight_ok = Or([And(from_city == city_map[a], to_city == city_map[b]) for (a, b) in allowed_flights])
        s.add(If(from_city != to_city, flight_ok, True))
    
    # Solve and output itinerary
    if s.check() == sat:
        m = s.model()
        result = []
        for i in range(n_days):
            city_val = m[itinerary[i]]
            city_name = None
            for name, const in city_map.items():
                if const.eq(city_val):
                    city_name = name
                    break
            result.append({"day": i+1, "place": city_name})
        output = {"itinerary": result}
        print(json.dumps(output))
    else:
        print('{"itinerary": []}')

if __name__ == '__main__':
    main()