from z3 import *

def main():
    s = Solver()
    days = 12
    cities = ['Geneva', 'Split', 'Helsinki', 'Vilnius', 'Reykjavik']
    required_days = {
        'Geneva': 6,
        'Split': 2,
        'Helsinki': 2,
        'Vilnius': 3,
        'Reykjavik': 3
    }
    
    in_city = {}
    for d in range(1, days+1):
        for c in cities:
            in_city[(d, c)] = Bool(f"in_{d}_{c}")
    
    flight_days = [Bool(f"flight_{d}") for d in range(1, days+1)]
    
    for d in range(1, days+1):
        in_cities_today = [in_city[(d, c)] for c in cities]
        count = Sum([If(v, 1, 0) for v in in_cities_today])
        s.add(flight_days[d-1] == (count == 2))
        s.add(Or(count == 1, count == 2))
    
    s.add(Sum([If(flight_days[d-1], 1, 0) for d in range(1, days+1)]) == 4)
    
    for c in cities:
        total = Sum([If(in_city[(d, c)], 1, 0) for d in range(1, days+1)])
        s.add(total == required_days[c])
    
    s.add(in_city[(7, 'Vilnius')] == True)
    s.add(in_city[(8, 'Vilnius')] == True)
    s.add(in_city[(9, 'Vilnius')] == True)
    s.add(in_city[(10, 'Reykjavik')] == True)
    s.add(in_city[(11, 'Reykjavik')] == True)
    s.add(in_city[(12, 'Reykjavik')] == True)
    
    direct_flights = [
        ('Split', 'Helsinki'),
        ('Geneva', 'Split'),
        ('Geneva', 'Helsinki'),
        ('Helsinki', 'Reykjavik'),
        ('Vilnius', 'Helsinki'),
        ('Split', 'Vilnius')
    ]
    flight_pairs = set()
    for (a, b) in direct_flights:
        flight_pairs.add((a, b))
        flight_pairs.add((b, a))
    
    for d in range(1, days+1):
        for i in range(len(cities)):
            for j in range(i+1, len(cities)):
                c1 = cities[i]
                c2 = cities[j]
                if (c1, c2) not in flight_pairs:
                    s.add(Not(And(in_city[(d, c1)], in_city[(d, c2)])))
    
    for d in range(1, days):
        for c in cities:
            s.add(Implies(
                And(in_city[(d+1, c)], Not(in_city[(d, c)])),
                And(in_city[(d, c)], flight_days[d-1])
            ))
    
    if s.check() == sat:
        model = s.model()
        blocks = {}
        for city in cities:
            days_present = []
            for d in range(1, days+1):
                if is_true(model[in_city[(d, city)]]):
                    days_present.append(d)
            if not days_present:
                continue
            days_present.sort()
            cont_blocks = []
            start = days_present[0]
            end = days_present[0]
            for i in range(1, len(days_present)):
                if days_present[i] == end + 1:
                    end = days_present[i]
                else:
                    cont_blocks.append((start, end))
                    start = days_present[i]
                    end = days_present[i]
            cont_blocks.append((start, end))
            blocks[city] = cont_blocks
        
        itinerary = []
        for city in cities:
            if city in blocks:
                for (start, end) in blocks[city]:
                    if start == end:
                        dr_str = f"Day {start}"
                    else:
                        dr_str = f"Day {start}-{end}"
                    itinerary.append({"day_range": dr_str, "place": city})
        
        for d in range(1, days+1):
            cities_today = []
            for city in cities:
                if is_true(model[in_city[(d, city)]]):
                    cities_today.append(city)
            if len(cities_today) == 2:
                for city in cities_today:
                    itinerary.append({"day_range": f"Day {d}", "place": city})
        
        def get_first_day(record):
            dr = record["day_range"]
            if '-' in dr:
                return int(dr.split('-')[0].split()[1])
            else:
                return int(dr.split()[1])
        
        itinerary_sorted = sorted(itinerary, key=get_first_day)
        output = {"itinerary": itinerary_sorted}
        print(output)
    else:
        print("No solution found")

if __name__ == "__main__":
    main()