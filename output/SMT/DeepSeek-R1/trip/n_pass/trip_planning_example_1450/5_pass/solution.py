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
    
    # Krakow event constraints
    for i in range(5, 10):  # Days 5-9: full days
        solver.add(s[i] == city_map['Krakow'])
        solver.add(e[i] == city_map['Krakow'])
    # Outside event days: no full days in Krakow
    for i in list(range(1, 5)) + list(range(10, 33)):
        solver.add(z3.Or(s[i] != city_map['Krakow'], e[i] != city_map['Krakow']))
    
    # Istanbul event constraints
    for i in range(25, 30):  # Days 25-29: full days
        solver.add(s[i] == city_map['Istanbul'])
        solver.add(e[i] == city_map['Istanbul'])
    # Outside event days: no full days in Istanbul
    for i in list(range(1, 25)) + list(range(30, 33)):
        solver.add(z3.Or(s[i] != city_map['Istanbul'], e[i] != city_map['Istanbul']))
    
    # Duration constraints (count only full days)
    for city_name in cities:
        c = city_map[city_name]
        total_full_days = 0
        for i in range(1, 33):
            full_day = z3.And(s[i] == c, e[i] == c)
            total_full_days += z3.If(full_day, 1, 0)
        solver.add(total_full_days == req_days[city_name])
    
    if solver.check() == z3.sat:
        model = solver.model()
        itinerary_list = []
        day = 1
        while day <= 32:
            s_val = model.eval(s[day])
            e_val = model.eval(e[day])
            if s_val == e_val:  # Full day
                start_day = day
                current_city = s_val
                while day <= 32 and model.eval(s[day]) == current_city and model.eval(e[day]) == current_city:
                    day += 1
                end_day = day - 1
                itinerary_list.append({
                    "day_range": f"Day {start_day}-{end_day}",
                    "place": str(current_city)
                })
            else:  # Travel day
                itinerary_list.append({"day_range": f"Day {day}", "place": str(s_val)})
                itinerary_list.append({"day_range": f"Day {day}", "place": str(e_val)})
                day += 1
        
        result = {'itinerary': itinerary_list}
        print(json.dumps(result, indent=2))
    else:
        print("No solution found")

if __name__ == '__main__':
    main()