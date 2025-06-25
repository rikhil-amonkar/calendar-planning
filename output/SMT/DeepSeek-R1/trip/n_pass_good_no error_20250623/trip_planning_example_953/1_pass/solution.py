from z3 import *

def main():
    cities = ['Barcelona', 'Florence', 'Frankfurt', 'Salzburg', 'Stockholm', 'Stuttgart', 'Venice']
    required_days = [2, 4, 4, 4, 2, 3, 5]
    
    direct_flights = [
        ('Barcelona', 'Frankfurt'),
        ('Florence', 'Frankfurt'),
        ('Stockholm', 'Barcelona'),
        ('Barcelona', 'Florence'),
        ('Venice', 'Barcelona'),
        ('Stuttgart', 'Barcelona'),
        ('Frankfurt', 'Salzburg'),
        ('Stockholm', 'Frankfurt'),
        ('Stuttgart', 'Stockholm'),
        ('Stuttgart', 'Frankfurt'),
        ('Venice', 'Stuttgart'),
        ('Venice', 'Frankfurt')
    ]
    
    direct_flights_set = set()
    for flight in direct_flights:
        c1, c2 = flight
        key = tuple(sorted([c1, c2]))
        direct_flights_set.add(key)
    
    n_days = 18
    n_cities = 7
    venice_index = cities.index('Venice')
    startable_indices = [cities.index(c) for c in ['Barcelona', 'Frankfurt', 'Stuttgart']]
    
    in_city = [[Bool(f"in_city_{i}_{j}") for j in range(n_cities)] for i in range(n_days)]
    solver = Solver()
    
    # At least one city per day, at most two
    for i in range(n_days):
        solver.add(Or(in_city[i]))
        for j1 in range(n_cities):
            for j2 in range(j1+1, n_cities):
                for j3 in range(j2+1, n_cities):
                    solver.add(Not(And(in_city[i][j1], in_city[i][j2], in_city[i][j3])))
    
    two_cities = [Bool(f"two_cities_{i}") for i in range(n_days)]
    for i in range(n_days):
        conditions = []
        for j1 in range(n_cities):
            for j2 in range(j1+1, n_cities):
                and_conditions = [in_city[i][j1], in_city[i][j2]]
                for j3 in range(n_cities):
                    if j3 != j1 and j3 != j2:
                        and_conditions.append(Not(in_city[i][j3]))
                conditions.append(And(and_conditions))
        solver.add(two_cities[i] == Or(conditions))
    solver.add(Sum([If(two_cities[i], 1, 0) for i in range(n_days)]) == 6)
    
    for j in range(n_cities):
        solver.add(Sum([If(in_city[i][j], 1, 0) for i in range(n_days)]) == required_days[j])
    
    for i in range(n_days):
        for j1 in range(n_cities):
            for j2 in range(j1+1, n_cities):
                c1 = cities[j1]
                c2 = cities[j2]
                key = tuple(sorted([c1, c2]))
                if key not in direct_flights_set:
                    solver.add(Not(And(two_cities[i], in_city[i][j1], in_city[i][j2])))
    
    for i in range(5):
        solver.add(in_city[i][venice_index] == True)
    for i in [1, 2, 3]:
        for j in range(n_cities):
            if j != venice_index:
                solver.add(in_city[i][j] == False)
        solver.add(two_cities[i] == False)
    
    solver.add(Or([in_city[0][j] for j in startable_indices]))
    solver.add(two_cities[0] == True)
    solver.add(Or([in_city[4][j] for j in startable_indices]))
    solver.add(two_cities[4] == True)
    
    if solver.check() == sat:
        model = solver.model()
        continuous_blocks = []
        for j in range(n_cities):
            days_in_c = []
            for i in range(n_days):
                if is_true(model.eval(in_city[i][j])):
                    days_in_c.append(i)
            if not days_in_c:
                continue
            days_in_c.sort()
            groups = []
            start = days_in_c[0]
            current = start
            for idx in range(1, len(days_in_c)):
                if days_in_c[idx] == current + 1:
                    current = days_in_c[idx]
                else:
                    groups.append((start, current))
                    start = days_in_c[idx]
                    current = days_in_c[idx]
            groups.append((start, current))
            for s, e in groups:
                if s == e:
                    continuous_blocks.append({
                        "day_range": f"Day {s+1}",
                        "place": cities[j]
                    })
                else:
                    continuous_blocks.append({
                        "day_range": f"Day {s+1}-{e+1}",
                        "place": cities[j]
                    })
        
        travel_records = []
        for i in range(n_days):
            if is_true(model.eval(two_cities[i])):
                for j in range(n_cities):
                    if is_true(model.eval(in_city[i][j])):
                        travel_records.append({
                            "day_range": f"Day {i+1}",
                            "place": cities[j]
                        })
        
        def get_start_day(record):
            s = record['day_range'].split()[1]
            if '-' in s:
                return int(s.split('-')[0])
            else:
                return int(s)
        
        continuous_blocks_sorted = sorted(continuous_blocks, key=get_start_day)
        travel_records_sorted = sorted(travel_records, key=lambda x: int(x['day_range'].split()[1]))
        itinerary_list = continuous_blocks_sorted + travel_records_sorted
        result = {"itinerary": itinerary_list}
        print(result)
    else:
        print("No solution found")

if __name__ == "__main__":
    main()