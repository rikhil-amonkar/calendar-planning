from z3 import *
import json

def main():
    CitySort = Datatype('CitySort')
    CitySort.declare('Brussels')
    CitySort.declare('Barcelona')
    CitySort.declare('Split')
    CitySort = CitySort.create()
    brussels = CitySort.Brussels
    barcelona = CitySort.Barcelona
    split = CitySort.Split
    
    city_map = {
        brussels: 'Brussels',
        barcelona: 'Barcelona',
        split: 'Split'
    }
    
    s = [None] * 13
    s[0] = brussels
    for i in range(1, 13):
        s[i] = Const(f's_{i}', CitySort)
    
    solver = Solver()
    
    direct_flights = [
        (brussels, barcelona),
        (barcelona, brussels),
        (barcelona, split),
        (split, barcelona)
    ]
    
    for i in range(0, 12):
        flight_taken = (s[i] != s[i+1])
        allowed_flight = Or([And(s[i] == dep, s[i+1] == arr) for dep, arr in direct_flights])
        solver.add(Implies(flight_taken, allowed_flight))
    
    in_brussels = []
    in_barcelona = []
    in_split = []
    for i in range(0, 12):
        in_brussels.append(Or(s[i] == brussels, s[i+1] == brussels))
        in_barcelona.append(Or(s[i] == barcelona, s[i+1] == barcelona))
        in_split.append(Or(s[i] == split, s[i+1] == split))
    
    total_brussels = Sum([If(in_brussels[i], 1, 0) for i in range(12)])
    total_barcelona = Sum([If(in_barcelona[i], 1, 0) for i in range(12)])
    total_split = Sum([If(in_split[i], 1, 0) for i in range(12)])
    
    solver.add(total_brussels == 2)
    solver.add(total_barcelona == 7)
    solver.add(total_split == 5)
    solver.add(in_brussels[1] == True)
    
    if solver.check() == sat:
        m = solver.model()
        overnight_cities = []
        for i in range(1, 13):
            c = m.eval(s[i])
            overnight_cities.append(city_map[c])
        
        blocks = []
        start = 1
        current_city = overnight_cities[0]
        for i in range(1, 12):
            if overnight_cities[i] != current_city:
                blocks.append((start, i, current_city))
                start = i + 1
                current_city = overnight_cities[i]
        blocks.append((start, 12, current_city))
        
        itinerary_list = []
        for (start_day, end_day, city) in blocks:
            day_range = f"Day {start_day}-{end_day}"
            itinerary_list.append({"day_range": day_range, "place": city})
        
        result = {"itinerary": itinerary_list}
        print(json.dumps(result))
    else:
        print('{"error": "No solution found"}')

if __name__ == "__main__":
    main()