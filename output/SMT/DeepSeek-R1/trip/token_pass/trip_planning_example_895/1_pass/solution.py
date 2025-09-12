from z3 import Solver, Int, Bool, Or, And, Implies, Not, If, sat
import json

def main():
    cities = ['Venice', 'London', 'Lisbon', 'Brussels', 'Reykjavik', 'Santorini', 'Madrid']
    city_index = {city: idx for idx, city in enumerate(cities)}
    index_city = {idx: city for city, idx in city_index.items()}
    
    direct_flights = set([
        ('Venice', 'Madrid'), ('Lisbon', 'Reykjavik'), ('Brussels', 'Venice'),
        ('Venice', 'Santorini'), ('Lisbon', 'Venice'), ('Reykjavik', 'Madrid'),
        ('Brussels', 'London'), ('Madrid', 'London'), ('Santorini', 'London'),
        ('London', 'Reykjavik'), ('Brussels', 'Lisbon'), ('Lisbon', 'London'),
        ('Lisbon', 'Madrid'), ('Madrid', 'Santorini'), ('Brussels', 'Reykjavik'),
        ('Brussels', 'Madrid'), ('Venice', 'London')
    ])
    
    direct_flights_symmetric = set()
    for (c1, c2) in direct_flights:
        direct_flights_symmetric.add((city_index[c1], city_index[c2]))
        direct_flights_symmetric.add((city_index[c2], city_index[c1]))
    
    n_days = 17
    solver = Solver()
    
    city_end = [Int(f'city_end_{d}') for d in range(1, n_days+1)]
    travel = [Bool(f'travel_{d}') for d in range(1, n_days+1)]
    
    for d in range(n_days):
        solver.add(city_end[d] >= 0, city_end[d] < 7)
    
    solver.add(city_end[0] == city_index['Brussels'])
    
    for d in range(1, n_days):
        solver.add(travel[d] == (city_end[d-1] != city_end[d]))
        conds = []
        for (i, j) in direct_flights_symmetric:
            conds.append(And(city_end[d-1] == i, city_end[d] == j))
        solver.add(Implies(travel[d], Or(conds)))
    
    total_days = [0] * 7
    for c_idx in range(7):
        total_days[c_idx] += If(city_end[0] == c_idx, 1, 0)
    
    for d in range(1, n_days):
        for c_idx in range(7):
            total_days[c_idx] += If(travel[d],
                If(city_end[d-1] == c_idx, 1, 0) + If(city_end[d] == c_idx, 1, 0),
                If(city_end[d] == c_idx, 1, 0))
    
    solver.add(total_days[city_index['Venice']] == 3)
    solver.add(total_days[city_index['London']] == 3)
    solver.add(total_days[city_index['Lisbon']] == 4)
    solver.add(total_days[city_index['Brussels']] == 2)
    solver.add(total_days[city_index['Reykjavik']] == 3)
    solver.add(total_days[city_index['Santorini']] == 3)
    solver.add(total_days[city_index['Madrid']] == 5)
    
    solver.add(city_end[1] == city_index['Brussels'])
    solver.add(Not(travel[1]))
    
    venice_conditions = []
    for d in [4,5,6]:
        venice_conditions.append(
            If(travel[d],
                Or(city_end[d-1] == city_index['Venice'], city_end[d] == city_index['Venice']),
                city_end[d] == city_index['Venice'])
        )
    solver.add(Or(venice_conditions))
    
    madrid_conditions = []
    for d in range(6, 11):
        madrid_conditions.append(
            If(travel[d],
                Or(city_end[d-1] == city_index['Madrid'], city_end[d] == city_index['Madrid']),
                city_end[d] == city_index['Madrid'])
        )
    solver.add(Or(madrid_conditions))
    
    if solver.check() == sat:
        model = solver.model()
        end_cities = []
        for d in range(n_days):
            val = model[city_end[d]].as_long()
            end_cities.append(index_city[val])
        
        itinerary = []
        start = 0
        for i in range(1, n_days):
            if end_cities[i] != end_cities[start]:
                day_range = f"Day {start+1}-{i}"
                itinerary.append({"day_range": day_range, "place": end_cities[start]})
                start = i
        day_range = f"Day {start+1}-{n_days}"
        itinerary.append({"day_range": day_range, "place": end_cities[start]})
        
        print(json.dumps({"itinerary": itinerary}))
    else:
        print('No solution found')

if __name__ == '__main__':
    main()