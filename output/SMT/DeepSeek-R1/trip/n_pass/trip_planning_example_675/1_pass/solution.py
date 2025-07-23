import z3

def main():
    # Define the city enum
    CitySort, (DUB, SPL, MIL, POR, KRA, MUN) = z3.EnumSort('City', ['DUB', 'SPL', 'MIL', 'POR', 'KRA', 'MUN'])
    city_names = ['DUB', 'SPL', 'MIL', 'POR', 'KRA', 'MUN']
    
    # Define the allowed direct flight pairs (bidirectional)
    allowed_pairs = [
        (MUN, POR), (POR, MUN),
        (SPL, MIL), (MIL, SPL),
        (MIL, POR), (POR, MIL),
        (MUN, KRA), (KRA, MUN),
        (MUN, MIL), (MIL, MUN),
        (DUB, MUN), (MUN, DUB),
        (KRA, SPL), (SPL, KRA),
        (KRA, MIL), (MIL, KRA),
        (MUN, SPL), (SPL, MUN)
    ]
    
    # Create Z3 solver
    solver = z3.Solver()
    
    # Variables: s[0] to s[15] for days 1 to 16, f[0] to f[14] for flights on days 1 to 15
    s = [z3.Const('s%d' % i, CitySort) for i in range(16)]
    f = [z3.Bool('f%d' % i) for i in range(15)]
    
    # Flight constraints
    for i in range(15):
        # If flying, the current and next city must be connected and different
        flight_condition = z3.Or([z3.And(s[i] == a, s[i+1] == b) for a, b in allowed_pairs])
        solver.add(z3.Implies(f[i], z3.And(s[i] != s[i+1], flight_condition)))
        # If not flying, the next day starts in the same city
        solver.add(z3.Implies(z3.Not(f[i]), s[i] == s[i+1]))
    
    # Duration constraints: count days in each city
    def count_days(city_const):
        count = 0
        # Count starting city days
        for i in range(16):
            count += z3.If(s[i] == city_const, 1, 0)
        # Count flight destination days
        for i in range(15):
            count += z3.If(z3.And(f[i], s[i+1] == city_const), 1, 0)
        return count
    
    solver.add(count_days(DUB) == 4)
    solver.add(count_days(SPL) == 3)
    solver.add(count_days(MIL) == 3)
    solver.add(count_days(POR) == 4)
    solver.add(count_days(KRA) == 2)
    solver.add(count_days(MUN) == 5)
    
    # Event constraints
    # Wedding in Milan between days 11-13 (inclusive)
    wedding_days = []
    for day in [11, 12, 13]:
        i = day - 1  # index in s: day11 -> s[10]
        # Flight index for the day: day11 flight is f[10] (if day=11, flight index = 10)
        # Condition: either start in Milan or fly to Milan on that day
        cond = z3.Or(s[i] == MIL, z3.And(f[i], s[i+1] == MIL))
        wedding_days.append(cond)
    solver.add(z3.Or(wedding_days))
    
    # Meeting in Krakow between days 8-9
    meeting_days = []
    for day in [8, 9]:
        i = day - 1
        cond = z3.Or(s[i] == KRA, z3.And(f[i], s[i+1] == KRA))
        meeting_days.append(cond)
    solver.add(z3.Or(meeting_days))
    
    # Show in Munich between days 4-8
    show_days = []
    for day in [4, 5, 6, 7, 8]:
        i = day - 1
        cond = z3.Or(s[i] == MUN, z3.And(f[i], s[i+1] == MUN))
        show_days.append(cond)
    solver.add(z3.Or(show_days))
    
    # Solve the constraints
    if solver.check() == z3.sat:
        model = solver.model()
        itinerary = []
        # Map Z3 constants to city names
        city_map = {}
        for city_const, name in zip([DUB, SPL, MIL, POR, KRA, MUN], city_names):
            city_map[model.eval(city_const).as_long()] = name
        
        for day in range(1, 17):
            idx = day - 1
            start_city_val = model.eval(s[idx])
            start_city_name = city_map[start_city_val.as_long()]
            if day < 16:
                flight_flag = model.eval(f[idx])
                if z3.is_true(flight_flag):
                    end_city_val = model.eval(s[idx+1])
                    end_city_name = city_map[end_city_val.as_long()]
                    cities = [start_city_name, end_city_name]
                else:
                    cities = [start_city_name]
            else:
                cities = [start_city_name]
            itinerary.append({"day": day, "cities": cities})
        
        # Output the itinerary as a JSON-formatted dictionary
        import json
        result = {'itinerary': itinerary}
        print(json.dumps(result, indent=2))
    else:
        print("No solution found")

if __name__ == '__main__':
    main()