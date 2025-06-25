from z3 import *

def main():
    City = Datatype('City')
    cities_list_str = ["Paris", "Florence", "Vienna", "Porto", "Munich", "Nice", "Warsaw"]
    for c in cities_list_str:
        City.declare(c)
    City = City.create()
    
    s = [Const('s_%d' % i, City) for i in range(1, 21)]
    e = [Const('e_%d' % i, City) for i in range(1, 21)]
    
    solver = Solver()
    
    # Fixed events: Porto on days 1-3
    for i in range(0, 3):
        solver.add(s[i] == City.Porto)
        solver.add(e[i] == City.Porto)
    
    # Fixed events: Warsaw on days 13-15
    for i in range(12, 15):
        solver.add(s[i] == City.Warsaw)
        solver.add(e[i] == City.Warsaw)
    
    # Fixed events: Vienna on days 19-20
    solver.add(s[18] == City.Vienna)
    solver.add(e[18] == City.Vienna)
    solver.add(s[19] == City.Vienna)
    solver.add(e[19] == City.Vienna)
    
    # Continuity: end of day i must equal start of day i+1
    for i in range(0, 19):
        solver.add(e[i] == s[i+1])
    
    # Direct flights
    direct_flights = [
        ("Florence", "Vienna"),
        ("Paris", "Warsaw"),
        ("Munich", "Vienna"),
        ("Porto", "Vienna"),
        ("Warsaw", "Vienna"),
        ("Florence", "Munich"),
        ("Munich", "Warsaw"),
        ("Munich", "Nice"),
        ("Paris", "Florence"),
        ("Warsaw", "Nice"),
        ("Porto", "Munich"),
        ("Porto", "Nice"),
        ("Paris", "Vienna"),
        ("Nice", "Vienna"),
        ("Porto", "Paris"),
        ("Paris", "Nice"),
        ("Paris", "Munich"),
        ("Porto", "Warsaw")
    ]
    flight_pairs = set()
    for a, b in direct_flights:
        c1 = getattr(City, a)
        c2 = getattr(City, b)
        flight_pairs.add((c1, c2))
        flight_pairs.add((c2, c1))
    
    for i in range(0, 20):
        solver.add(If(s[i] != e[i], Or([And(s[i] == c1, e[i] == c2) for (c1, c2) in flight_pairs]), True))
    
    # Total days per city
    total_days = []
    for city in [City.Paris, City.Florence, City.Vienna, City.Porto, City.Munich, City.Nice, City.Warsaw]:
        count_s = Sum([If(s[i] == city, 1, 0) for i in range(20)])
        count_e = Sum([If(And(e[i] == city, s[i] != city), 1, 0) for i in range(20)])
        total = count_s + count_e
        if city == City.Paris:
            total_days.append(total == 5)
        elif city == City.Florence:
            total_days.append(total == 3)
        elif city == City.Vienna:
            total_days.append(total == 2)
        elif city == City.Porto:
            total_days.append(total == 3)
        elif city == City.Munich:
            total_days.append(total == 5)
        elif city == City.Nice:
            total_days.append(total == 5)
        elif city == City.Warsaw:
            total_days.append(total == 3)
    solver.add(total_days)
    
    # Solve
    if solver.check() == sat:
        model = solver.model()
        s_vals = [model.eval(s_i) for s_i in s]
        e_vals = [model.eval(e_i) for e_i in e]
        cities_str = ["Paris", "Florence", "Vienna", "Porto", "Munich", "Nice", "Warsaw"]
        s_idx = [v.as_long() for v in s_vals]
        e_idx = [v.as_long() for v in e_vals]
        
        def format_day_range(start, end):
            if start == end:
                return f"Day {start}"
            else:
                return f"Day {start}-{end}"
        
        itinerary = []
        current_city = s_idx[0]
        start_day = 1
        for i in range(0, 20):
            if s_idx[i] != e_idx[i]:
                block_range = format_day_range(start_day, i+1)
                itinerary.append({"day_range": block_range, "place": cities_str[current_city]})
                itinerary.append({"day_range": f"Day {i+1}", "place": cities_str[s_idx[i]]})
                itinerary.append({"day_range": f"Day {i+1}", "place": cities_str[e_idx[i]]})
                current_city = e_idx[i]
                start_day = i+1
        block_range = format_day_range(start_day, 20)
        itinerary.append({"day_range": block_range, "place": cities_str[current_city]})
        
        result = {"itinerary": itinerary}
        print(result)
    else:
        print("No solution found")

if __name__ == "__main__":
    main()