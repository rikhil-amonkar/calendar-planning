import z3
import json

def main():
    cities = ["Stockholm", "Hamburg", "Florence", "Istanbul", "Oslo", "Vilnius", "Santorini", "Munich", "Frankfurt", "Krakow"]
    
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
    
    directed = [
        ("Krakow", "Vilnius"),
        ("Florence", "Munich"),
        ("Stockholm", "Santorini"),
        ("Santorini", "Oslo"),
        ("Vilnius", "Munich")
    ]
    
    allowed_flights = set()
    for (a, b) in bidirectional:
        allowed_flights.add((a, b))
        allowed_flights.add((b, a))
    for (a, b) in directed:
        allowed_flights.add((a, b))
    
    City, city_consts = z3.EnumSort('City', cities)
    city_map = {name: const for name, const in zip(cities, city_consts)}
    
    s = [None]
    e = [None]
    for i in range(1, 33):
        s.append(z3.Const(f's_{i}', City))
        e.append(z3.Const(f'e_{i}', City))
    
    solver = z3.Solver()
    
    for i in range(1, 32):
        solver.add(e[i] == s[i+1])
    
    for i in range(1, 33):
        start_city = s[i]
        end_city = e[i]
        same_city = (start_city == end_city)
        flight_conditions = []
        for (a, b) in allowed_flights:
            a_const = city_map[a]
            b_const = city_map[b]
            flight_conditions.append(z3.And(start_city == a_const, end_city == b_const))
        solver.add(z3.Or(same_city, z3.Or(flight_conditions)))
    
    # Fixed event in Krakow: Days 5-9
    solver.add(e[5] == city_map['Krakow'])  # Arrive by end of day 5
    solver.add(s[9] == city_map['Krakow'])  # Depart at start of day 9
    for i in [6, 7, 8]:  # Full days in Krakow
        solver.add(s[i] == city_map['Krakow'])
        solver.add(e[i] == city_map['Krakow'])
    for i in list(range(1, 5)) + list(range(10, 33)):  # No Krakow outside event
        solver.add(s[i] != city_map['Krakow'])
        solver.add(e[i] != city_map['Krakow'])
    
    # Fixed event in Istanbul: Days 25-29
    solver.add(e[25] == city_map['Istanbul'])  # Arrive by end of day 25
    solver.add(s[29] == city_map['Istanbul'])  # Depart at start of day 29
    for i in [26, 27, 28]:  # Full days in Istanbul
        solver.add(s[i] == city_map['Istanbul'])
        solver.add(e[i] == city_map['Istanbul'])
    for i in list(range(1, 25)) + list(range(30, 33)):  # No Istanbul outside event
        solver.add(s[i] != city_map['Istanbul'])
        solver.add(e[i] != city_map['Istanbul'])
    
    # Duration constraints
    for city_name in cities:
        c = city_map[city_name]
        total = 0
        for i in range(1, 33):
            in_city = z3.Or(s[i] == c, e[i] == c)
            total += z3.If(in_city, 1, 0)
        solver.add(total == req_days[city_name])
    
    if solver.check() == z3.sat:
        model = solver.model()
        itinerary_list = []
        current_city = None
        start_day = 1
        
        for day in range(1, 33):
            s_val = model.eval(s[day])
            e_val = model.eval(e[day])
            s_str = str(s_val)
            e_str = str(e_val)
            
            # Handle flight days
            if s_str != e_str:
                if current_city is not None:
                    # Finish previous city stay
                    end_day = day
                    itinerary_list.append({
                        "day_range": f"Day {start_day}-{end_day}",
                        "place": current_city
                    })
                    start_day = day + 1
                # Add flight day as single-day entries
                itinerary_list.append({"day_range": f"Day {day}", "place": s_str})
                itinerary_list.append({"day_range": f"Day {day}", "place": e_str})
                current_city = e_str
            elif current_city is None:
                current_city = s_str
            elif current_city != s_str:
                # City changed on a non-flight day (shouldn't happen)
                end_day = day - 1
                itinerary_list.append({
                    "day_range": f"Day {start_day}-{end_day}",
                    "place": current_city
                })
                current_city = s_str
                start_day = day
        
        # Add last city stay
        if current_city is not None:
            itinerary_list.append({
                "day_range": f"Day {start_day}-32",
                "place": current_city
            })
        
        result = {'itinerary': itinerary_list}
        print(json.dumps(result, indent=2))
    else:
        print("No solution found")

if __name__ == '__main__':
    main()