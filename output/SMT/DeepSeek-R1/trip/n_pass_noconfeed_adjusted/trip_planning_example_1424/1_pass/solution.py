from z3 import *
import json

def main():
    # City to index mapping
    cities = {
        'Amsterdam': 0,
        'Brussels': 1,
        'Helsinki': 2,
        'Lyon': 3,
        'Naples': 4,
        'Porto': 5,
        'Reykjavik': 6,
        'Split': 7,
        'Valencia': 8,
        'Warsaw': 9
    }
    
    index_to_city = {v: k for k, v in cities.items()}
    
    # Desired durations: [Amsterdam, Brussels, Helsinki, Lyon, Naples, Porto, Reykjavik, Split, Valencia, Warsaw]
    durations = [4, 3, 4, 3, 4, 5, 5, 3, 2, 3]
    
    # Direct flights (as list of tuples)
    direct_flights_list = [
        (0,9), (2,1), (2,9), (6,1), (0,3), (0,4), (0,6), (4,8), (5,1), (0,7),
        (3,7), (9,7), (5,0), (2,7), (1,3), (5,3), (6,9), (1,8), (8,3), (5,9),
        (9,8), (0,2), (5,8), (9,1), (9,4), (4,7), (2,4), (2,6), (0,8), (4,1)
    ]
    
    # Create symmetric direct flights set (both orders)
    direct_flights_set = set()
    for (a, b) in direct_flights_list:
        direct_flights_set.add((a, b))
        direct_flights_set.add((b, a))
    
    # Create two solvers for k=2 and k=3 cases
    solvers = [Solver() for _ in range(2)]
    solutions = []
    
    for case, solver in enumerate(solvers):
        # Sequence of cities for 10 stays
        s = [Int('s_%d' % i) for i in range(10)]
        
        # Fixed stays
        solver.add(s[0] == cities['Porto'])
        solver.add(s[1] == cities['Amsterdam'])
        solver.add(s[2] == cities['Helsinki'])
        if case == 0:  # k=2
            solver.add(s[5] == cities['Naples'])
            solver.add(s[6] == cities['Brussels'])
        else:  # k=3
            solver.add(s[6] == cities['Naples'])
            solver.add(s[7] == cities['Brussels'])
        
        # Remaining cities: Lyon, Reykjavik, Split, Valencia, Warsaw
        remaining_cities = [cities[c] for c in ['Lyon', 'Reykjavik', 'Split', 'Valencia', 'Warsaw']]
        
        # Constraints for the gap stays
        if case == 0:
            # k=2: first gap has 2 cities (s3, s4), second gap has 3 cities (s7, s8, s9)
            gap1 = [s[3], s[4]]
            gap2 = [s[7], s[8], s[9]]
            # All gap stays must be distinct and from remaining cities
            solver.add(Distinct(gap1 + gap2))
            for city in gap1 + gap2:
                solver.add(Or([city == rc for rc in remaining_cities]))
        else:
            # k=3: first gap has 3 cities (s3, s4, s5), second gap has 2 cities (s8, s9)
            gap1 = [s[3], s[4], s[5]]
            gap2 = [s[8], s[9]]
            solver.add(Distinct(gap1 + gap2))
            for city in gap1 + gap2:
                solver.add(Or([city == rc for rc in remaining_cities]))
        
        # Start and end days for each stay
        start = [Int('start_%d' % i) for i in range(10)]
        end = [Int('end_%d' % i) for i in range(10)]
        
        # Fixed start and end days for known stays
        solver.add(start[0] == 1, end[0] == 5)
        solver.add(start[1] == 5, end[1] == 8)
        solver.add(start[2] == 8, end[2] == 11)
        if case == 0:
            solver.add(start[5] == 17, end[5] == 20)
            solver.add(start[6] == 20, end[6] == 22)
            solver.add(start[7] == 22)
            solver.add(end[9] == 27)
        else:
            solver.add(start[6] == 17, end[6] == 20)
            solver.add(start[7] == 20, end[7] == 22)
            solver.add(start[8] == 22)
            solver.add(end[9] == 27)
        
        # Constraints for the gap stays
        if case == 0:
            # First gap: two cities
            solver.add(start[3] == 11)
            solver.add(end[3] == start[3] + durations[s[3]] - 1)
            solver.add(start[4] == end[3])
            solver.add(end[4] == start[4] + durations[s[4]] - 1)
            solver.add(end[4] == 17)  # End of first gap
            # Second gap: three cities
            solver.add(end[7] == start[7] + durations[s[7]] - 1)
            solver.add(start[8] == end[7])
            solver.add(end[8] == start[8] + durations[s[8]] - 1)
            solver.add(start[9] == end[8])
            solver.add(end[9] == start[9] + durations[s[9]] - 1)
        else:
            # First gap: three cities
            solver.add(start[3] == 11)
            solver.add(end[3] == start[3] + durations[s[3]] - 1)
            solver.add(start[4] == end[3])
            solver.add(end[4] == start[4] + durations[s[4]] - 1)
            solver.add(start[5] == end[4])
            solver.add(end[5] == start[5] + durations[s[5]] - 1)
            solver.add(end[5] == 17)  # End of first gap
            # Second gap: two cities
            solver.add(end[8] == start[8] + durations[s[8]] - 1)
            solver.add(start[9] == end[8])
            solver.add(end[9] == start[9] + durations[s[9]] - 1)
        
        # Direct flight constraints between consecutive stays
        for i in range(9):
            allowed = []
            for pair in direct_flights_set:
                allowed.append(And(s[i] == pair[0], s[i+1] == pair[1]))
            solver.add(Or(allowed))
        
        # Check satisfiability
        if solver.check() == sat:
            model = solver.model()
            sol_s = [model.evaluate(s[i]).as_long() for i in range(10)]
            sol_start = [model.evaluate(start[i]).as_long() for i in range(10)]
            sol_end = [model.evaluate(end[i]).as_long() for i in range(10)]
            
            # Build itinerary
            itinerary = []
            for i in range(10):
                city_index = sol_s[i]
                city_name = index_to_city[city_index]
                s_day = sol_start[i]
                e_day = sol_end[i]
                day_range = f"Day {s_day}-{e_day}"
                itinerary.append({"day_range": day_range, "place": city_name})
            
            solutions.append(itinerary)
            break
    
    if solutions:
        result = {"itinerary": solutions[0]}
        print(json.dumps(result))
    else:
        print('{"itinerary": []}')

if __name__ == "__main__":
    main()