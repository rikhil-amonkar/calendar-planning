from z3 import *
import json

def main():
    cities = ["Vienna", "Milan", "Rome", "Riga", "Lisbon", "Vilnius", "Oslo"]
    City, (Vienna, Milan, Rome, Riga, Lisbon, Vilnius, Oslo) = EnumSort('City', cities)
    city_map = {name: const for name, const in zip(cities, [Vienna, Milan, Rome, Riga, Lisbon, Vilnius, Oslo])}
    
    # Define flight connections (bidirectional and directed)
    bidirectional_connections = [
        ("Riga", "Oslo"), ("Vienna", "Milan"), ("Vienna", "Vilnius"), 
        ("Vienna", "Lisbon"), ("Riga", "Milan"), ("Lisbon", "Oslo"),
        ("Rome", "Lisbon"), ("Vienna", "Riga"), ("Vienna", "Rome"),
        ("Milan", "Oslo"), ("Vienna", "Oslo"), ("Vilnius", "Oslo"),
        ("Vilnius", "Milan"), ("Riga", "Lisbon"), ("Milan", "Lisbon")
    ]
    directed_connections = [("Rome", "Riga"), ("Riga", "Vilnius")]
    
    allowed_pairs = []
    for a, b in bidirectional_connections:
        allowed_pairs.append((city_map[a], city_map[b]))
        allowed_pairs.append((city_map[b], city_map[a]))
    for a, b in directed_connections:
        allowed_pairs.append((city_map[a], city_map[b]))
    
    # Create solver and itinerary variables
    n_days = 15
    itinerary = [Const(f'day_{i}', City) for i in range(n_days)]
    s = Solver()
    
    # Define presence in city for each day
    def in_city(city, day):
        if day == 0:
            # Day 1: start in Vienna, end in itinerary[0]
            return Or(city == Vienna, itinerary[0] == city)
        else:
            # Start is end of previous day, end is current day
            return Or(itinerary[day-1] == city, itinerary[day] == city)
    
    # Flight constraints
    # Day 1 flight: from Vienna to itinerary[0]
    s.add(If(Vienna != itinerary[0], 
             Or([And(Vienna == f, itinerary[0] == t) for (f, t) in allowed_pairs]), 
             True))
    
    # Flights for subsequent days
    for i in range(1, n_days):
        from_city = itinerary[i-1]
        to_city = itinerary[i]
        flight_ok = Or([And(from_city == f, to_city == t) for (f, t) in allowed_pairs])
        s.add(If(from_city != to_city, flight_ok, True))
    
    # Total days per city
    total_days = {}
    for city in [Vienna, Milan, Rome, Riga, Lisbon, Vilnius, Oslo]:
        total_days[city] = Sum([If(in_city(city, d), 1, 0) for d in range(n_days)])
    
    s.add(total_days[Vienna] == 4)
    s.add(total_days[Milan] == 2)
    s.add(total_days[Rome] == 3)
    s.add(total_days[Riga] == 2)
    s.add(total_days[Lisbon] == 3)
    s.add(total_days[Vilnius] == 4)
    s.add(total_days[Oslo] == 3)
    
    # Fixed events
    # Must be in Vienna on days 1 and 4 (presence-based)
    s.add(in_city(Vienna, 0))  # Day 1
    s.add(in_city(Vienna, 3))  # Day 4
    
    # Must be in Lisbon for at least one day between 11-13
    s.add(Or(in_city(Lisbon, 10), in_city(Lisbon, 11), in_city(Lisbon, 12)))
    
    # Must be in Oslo for at least one day between 13-15
    s.add(Or(in_city(Oslo, 12), in_city(Oslo, 13), in_city(Oslo, 14)))
    
    # Solve and format output
    if s.check() == sat:
        m = s.model()
        day_cities = []
        for i in range(n_days):
            city_val = m[itinerary[i]]
            for name, const in city_map.items():
                if const.eq(city_val):
                    day_cities.append(name)
                    break
        
        # Group consecutive days
        grouped = []
        start_day = 0
        current_city = day_cities[0]
        for i in range(1, n_days):
            if day_cities[i] != current_city:
                end_day = i - 1
                day_range = f"Day {start_day+1}-{end_day+1}" if start_day != end_day else f"Day {start_day+1}"
                grouped.append({"day_range": day_range, "place": current_city})
                start_day = i
                current_city = day_cities[i]
        end_day = n_days - 1
        day_range = f"Day {start_day+1}-{end_day+1}" if start_day != end_day else f"Day {start_day+1}"
        grouped.append({"day_range": day_range, "place": current_city})
        
        print(json.dumps({"itinerary": grouped}))
    else:
        print('{"itinerary": []}')

if __name__ == '__main__':
    main()