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
        in_brussels_i = Or(s[i] == brussels, s[i+1] == brussels)
        in_barcelona_i = Or(s[i] == barcelona, s[i+1] == barcelona)
        in_split_i = Or(s[i] == split, s[i+1] == split)
        in_brussels.append(in_brussels_i)
        in_barcelona.append(in_barcelona_i)
        in_split.append(in_split_i)
    
    solver.add(in_brussels[0] == True)
    solver.add(in_brussels[1] == True)
    for i in range(2, 12):
        solver.add(in_brussels[i] == False)
    
    total_barcelona = Sum([If(in_barcelona[i], 1, 0) for i in range(0, 12)])
    total_split = Sum([If(in_split[i], 1, 0) for i in range(0, 12)])
    solver.add(total_barcelona == 7)
    solver.add(total_split == 5)
    
    if solver.check() == sat:
        m = solver.model()
        overnight_stays = []
        for i in range(1, 13):
            c = m.eval(s[i])
            overnight_stays.append(city_map[c])
        
        blocks = []
        start_index = 0
        current_city = overnight_stays[0]
        for i in range(1, len(overnight_stays)):
            if overnight_stays[i] != current_city:
                end_index = i - 1
                start_day = start_index + 1
                end_day = end_index + 1
                if start_day == end_day:
                    day_range = f"Day {start_day}"
                else:
                    day_range = f"Day {start_day}-{end_day}"
                blocks.append({'day_range': day_range, 'place': current_city})
                start_index = i
                current_city = overnight_stays[i]
        start_day = start_index + 1
        end_day = len(overnight_stays)
        if start_day == end_day:
            day_range = f"Day {start_day}"
        else:
            day_range = f"Day {start_day}-{end_day}"
        blocks.append({'day_range': day_range, 'place': current_city})
        
        result = {"itinerary": blocks}
        print(json.dumps(result))
    else:
        print('{"error": "No solution found"}')

if __name__ == "__main__":
    main()