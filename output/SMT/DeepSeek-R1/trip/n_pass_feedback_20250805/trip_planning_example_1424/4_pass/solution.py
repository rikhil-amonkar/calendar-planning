from z3 import *
import json

def main():
    cities = ['Warsaw', 'Porto', 'Naples', 'Brussels', 'Split', 'Reykjavik', 'Amsterdam', 'Lyon', 'Helsinki', 'Valencia']
    city_to_index = {city: idx for idx, city in enumerate(cities)}
    required_days = [3, 5, 4, 3, 3, 5, 4, 3, 4, 2]
    
    flight_strings = [
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
    
    flight_pairs_set = set()
    for s in flight_strings:
        parts = s.split(' and ')
        c1, c2 = parts[0], parts[1]
        i1, i2 = city_to_index[c1], city_to_index[c2]
        if i1 > i2:
            i1, i2 = i2, i1
        flight_pairs_set.add((i1, i2))
    
    connected = [[] for _ in range(10)]
    for (i, j) in flight_pairs_set:
        connected[i].append(j)
        connected[j].append(i)
    
    s = Solver()
    in_city = [[Bool(f'in_d{d}_c{c}') for c in range(10)] for d in range(27)]
    
    for d in range(27):
        s.add(Or([in_city[d][c] for c in range(10)]))
        bools = [in_city[d][c] for c in range(10)]
        s.add(PbLe([(b, 1) for b in bools], 2))
    
    for c in range(10):
        total = Sum([If(in_city[d][c], 1, 0) for d in range(27)])
        s.add(total == required_days[c])
    
    for d in range(27):
        for i in range(10):
            for j in range(i+1, 10):
                if (i, j) not in flight_pairs_set:
                    s.add(Not(And(in_city[d][i], in_city[d][j])))
    
    for d in range(26):
        for c in range(10):
            leave_cond = Implies(
                And(in_city[d][c], Not(in_city[d+1][c])),
                Or([in_city[d+1][n] for n in connected[c]])
            )
            s.add(leave_cond)
    
    # Enforce consecutive stays for each city
    for c in range(10):
        for d in range(26):
            s.add(Implies(
                And(in_city[d][c], Not(in_city[d+1][c])),
                And([Not(in_city[j][c]) for j in range(d+2, 27)])
            )
    
    # Event constraints
    for d in range(0, 5):  # Porto: Days 1-5
        s.add(in_city[d][city_to_index['Porto']])
    
    for d in range(4, 8):  # Amsterdam: Days 5-8
        s.add(in_city[d][city_to_index['Amsterdam']])
    
    for d in range(7, 11):  # Helsinki: Days 8-11
        s.add(in_city[d][city_to_index['Helsinki']])
    
    for d in [16, 17, 18, 19]:  # Naples: Days 17-20
        s.add(in_city[d][city_to_index['Naples']])
    
    for d in [19, 20, 21]:  # Brussels: Days 20-22
        s.add(in_city[d][city_to_index['Brussels']])
    
    if s.check() == sat:
        m = s.model()
        # Extract all city stays
        stays = []
        for c in range(10):
            days = [d for d in range(27) if m.evaluate(in_city[d][c])]
            if not days:
                continue
            start = min(days)
            end = max(days)
            stays.append({
                'city': cities[c],
                'start': start,
                'end': end
            })
        
        # Sort by start day
        stays.sort(key=lambda x: x['start'])
        
        # Format as day ranges
        itinerary = []
        for stay in stays:
            start_day = stay['start'] + 1
            end_day = stay['end'] + 1
            if start_day == end_day:
                day_range = f"Day {start_day}"
            else:
                day_range = f"Day {start_day}-{end_day}"
            itinerary.append({'day_range': day_range, 'place': stay['city']})
        
        print(json.dumps({'itinerary': itinerary}, indent=2))
    else:
        print("No solution found")

if __name__ == '__main__':
    main()