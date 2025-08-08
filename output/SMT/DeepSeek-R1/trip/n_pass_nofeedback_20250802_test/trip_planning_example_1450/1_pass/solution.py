import z3
import json

def main():
    cities = ["Stockholm", "Hamburg", "Florence", "Istanbul", "Oslo", "Vilnius", "Santorini", "Munich", "Frankfurt", "Krakow"]
    
    # Required days per city
    req_days = {
        "Stockholm": 3,
        "Hamburg": 5,
        "Florence": 2,
        "Istanbul": 5,
        "Oslo": 5,
        "Vilnius": 5,
        "Santorini": 2,
        "Munich": 5,
        "Frankfurt": 4,
        "Krakow": 5
    }
    
    # Bidirectional flight connections (add both directions)
    bidirectional = [
        ("Oslo", "Stockholm"),
        ("Krakow", "Frankfurt"),
        ("Krakow", "Istanbul"),
        ("Munich", "Stockholm"),
        ("Hamburg", "Stockholm"),
        ("Oslo", "Istanbul"),
        ("Istanbul", "Stockholm"),
        ("Oslo", "Krakow"),
        ("Vilnius", "Istanbul"),
        ("Frankfurt", "Istanbul"),
        ("Oslo", "Frankfurt"),
        ("Munich", "Hamburg"),
        ("Munich", "Istanbul"),
        ("Oslo", "Munich"),
        ("Frankfurt", "Florence"),
        ("Oslo", "Hamburg"),
        ("Vilnius", "Frankfurt"),
        ("Krakow", "Munich"),
        ("Hamburg", "Istanbul"),
        ("Frankfurt", "Stockholm"),
        ("Frankfurt", "Munich"),
        ("Frankfurt", "Hamburg")
    ]
    
    # Directed flight connections (only one direction)
    directed = [
        ("Krakow", "Vilnius"),
        ("Florence", "Munich"),
        ("Stockholm", "Santorini"),
        ("Santorini", "Oslo"),
        ("Vilnius", "Munich")
    ]
    
    # Create the set of allowed directed flights
    allowed_flights = set()
    for (a, b) in bidirectional:
        allowed_flights.add((a, b))
        allowed_flights.add((b, a))
    for (a, b) in directed:
        allowed_flights.add((a, b))
    
    # Declare City enum
    City, (Stockholm, Hamburg, Florence, Istanbul, Oslo, Vilnius, Santorini, Munich, Frankfurt, Krakow) = z3.EnumSort('City', cities)
    city_map = {
        "Stockholm": Stockholm,
        "Hamburg": Hamburg,
        "Florence": Florence,
        "Istanbul": Istanbul,
        "Oslo": Oslo,
        "Vilnius": Vilnius,
        "Santorini": Santorini,
        "Munich": Munich,
        "Frankfurt": Frankfurt,
        "Krakow": Krakow
    }
    
    # Create Z3 variables for start and end cities for each day
    s = [None]  # index 0 unused
    e = [None]  # index 0 unused
    for i in range(1, 33):
        s.append(z3.Const('s_' + str(i), City))
        e.append(z3.Const('e_' + str(i), City))
    
    solver = z3.Solver()
    
    # Constraint: end city of day i is start city of day i+1
    for i in range(1, 32):
        solver.add(e[i] == s[i+1])
    
    # Flight constraints: if start and end differ, flight must be allowed
    for i in range(1, 33):
        start_city = s[i]
        end_city = e[i]
        # Condition for no flight or allowed flight
        flight_cond = z3.Or([z3.And(start_city == city_map[a], end_city == city_map[b]) for (a, b) in allowed_flights])
        solver.add(z3.Or(start_city == end_city, flight_cond))
    
    # Fixed events in Krakow (days 5-9)
    for i in range(5, 10):
        solver.add(z3.Or(s[i] == Krakow, e[i] == Krakow))
    for i in list(range(1, 5)) + list(range(10, 33)):
        solver.add(s[i] != Krakow, e[i] != Krakow)
    
    # Fixed events in Istanbul (days 25-29)
    for i in range(25, 30):
        solver.add(z3.Or(s[i] == Istanbul, e[i] == Istanbul))
    for i in list(range(1, 25)) + list(range(30, 33)):
        solver.add(s[i] != Istanbul, e[i] != Istanbul)
    
    # Total days constraint for each city
    for city_name in cities:
        c = city_map[city_name]
        total = 0
        for i in range(1, 33):
            total += z3.If(z3.Or(s[i] == c, e[i] == c), 1, 0)
        solver.add(total == req_days[city_name])
    
    # Check and get model
    if solver.check() == z3.sat:
        model = solver.model()
        itinerary_list = []
        # Map Z3 constants to city names
        reverse_map = {city_map[name]: name for name in cities}
        
        for i in range(1, 33):
            s_val = model.eval(s[i])
            e_val = model.eval(e[i])
            s_name = reverse_map[s_val]
            e_name = reverse_map[e_val]
            itinerary_list.append({"day": i, "place": s_name})
            if s_name != e_name:
                itinerary_list.append({"day": i, "place": e_name})
        
        result = {'itinerary': itinerary_list}
        print(json.dumps(result, indent=2))
    else:
        print("No solution found")

if __name__ == '__main__':
    main()