import z3

def main():
    cities = [
        'Warsaw', 'Porto', 'Naples', 'Brussels', 'Split', 
        'Reykjavik', 'Amsterdam', 'Lyon', 'Helsinki', 'Valencia'
    ]
    
    required_days = {
        'Warsaw': 3,
        'Porto': 5,
        'Naples': 4,
        'Brussels': 3,
        'Split': 3,
        'Reykjavik': 5,
        'Amsterdam': 4,
        'Lyon': 3,
        'Helsinki': 4,
        'Valencia': 2
    }
    
    flight_connections = [
        "Amsterdam and Warsaw", "Helsinki and Brussels", "Helsinki and Warsaw",
        "Reykjavik and Brussels", "Amsterdam and Lyon", "Amsterdam and Naples",
        "Amsterdam and Reykjavik", "Naples and Valencia", "Porto and Brussels",
        "Amsterdam and Split", "Lyon and Split", "Warsaw and Split",
        "Porto and Amsterdam", "Helsinki and Split", "Brussels and Lyon",
        "Porto and Lyon", "Reykjavik and Warsaw", "Brussels and Valencia",
        "Valencia and Lyon", "Porto and Warsaw", "Warsaw and Valencia",
        "Amsterdam and Helsinki", "Porto and Valencia", "Warsaw and Brussels",
        "Warsaw and Naples", "Naples and Split", "Helsinki and Naples",
        "Helsinki and Reykjavik", "Amsterdam and Valencia", "Naples and Brussels"
    ]
    
    flight_set_str = set()
    for conn in flight_connections:
        c1, c2 = conn.split(' and ')
        flight_set_str.add((c1, c2))
        flight_set_str.add((c2, c1))
    
    allowed_pairs = set()
    for (c1, c2) in flight_set_str:
        if c1 == c2:
            continue
        idx1 = cities.index(c1)
        idx2 = cities.index(c2)
        allowed_pairs.add((idx1, idx2))
    
    s = [z3.Int(f's_{i}') for i in range(28)]
    solver = z3.Solver()
    
    for i in range(28):
        solver.add(s[i] >= 0, s[i] < 10)
    
    for i in range(1, 28):
        stay_condition = (s[i-1] == s[i])
        fly_conditions = []
        for (idx1, idx2) in allowed_pairs:
            fly_conditions.append(z3.And(s[i-1] == idx1, s[i] == idx2))
        solver.add(z3.Or(stay_condition, z3.Or(fly_conditions)))
    
    for j in range(len(cities)):
        total = 0
        for i in range(1, 28):
            total += z3.If(z3.Or(s[i-1] == j, s[i] == j), 1, 0)
        solver.add(total == required_days[cities[j]])
    
    naples_idx = cities.index('Naples')
    for day in [17, 18, 19, 20]:
        solver.add(z3.Or(s[day-1] == naples_idx, s[day] == naples_idx))
    
    brussels_idx = cities.index('Brussels')
    for day in [20, 21, 22]:
        solver.add(z3.Or(s[day-1] == brussels_idx, s[day] == brussels_idx))
    
    porto_idx = cities.index('Porto')
    porto_or_conditions = []
    for day in range(1, 6):
        porto_or_conditions.append(z3.Or(s[day-1] == porto_idx, s[day] == porto_idx))
    solver.add(z3.Or(porto_or_conditions))
    
    amsterdam_idx = cities.index('Amsterdam')
    ams_or_conditions = []
    for day in range(5, 9):
        ams_or_conditions.append(z3.Or(s[day-1] == amsterdam_idx, s[day] == amsterdam_idx))
    solver.add(z3.Or(ams_or_conditions))
    
    helsinki_idx = cities.index('Helsinki')
    hel_or_conditions = []
    for day in range(8, 12):
        hel_or_conditions.append(z3.Or(s[day-1] == helsinki_idx, s[day] == helsinki_idx))
    solver.add(z3.Or(hel_or_conditions))
    
    if solver.check() == z3.sat:
        model = solver.model()
        state_seq = []
        for i in range(28):
            val = model.evaluate(s[i])
            state_seq.append(val.as_long())
        
        itinerary = []
        for day in range(1, 28):
            start_city_idx = state_seq[day-1]
            end_city_idx = state_seq[day]
            if start_city_idx == end_city_idx:
                places = [cities[start_city_idx]]
            else:
                places = sorted([cities[start_city_idx], [end_city_idx]])
            itinerary.append({"day": day, "place": places})
        
        result = {
            'itinerary': itinerary
        }
        print(result)
    else:
        print("No solution found")

if __name__ == "__main__":
    main()