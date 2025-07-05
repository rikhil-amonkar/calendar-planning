from z3 import *

def solve_itinerary():
    # Cities
    Valencia, Athens, Naples, Zurich = 0, 1, 2, 3
    cities = ['Valencia', 'Athens', 'Naples', 'Zurich']
    num_cities = len(cities)
    
    # Direct flights
    direct_flights = {
        Valencia: [Naples, Athens, Zurich],
        Athens: [Valencia, Naples, Zurich],
        Naples: [Valencia, Athens, Zurich],
        Zurich: [Naples, Athens, Valencia]
    }
    
    total_days = 20
    
    # Adjusted day requirements
    required_days = {
        Valencia: 4,
        Athens: 6,
        Naples: 5,
        Zurich: 3
    }
    
    day = [Int(f'day_{i+1}') for i in range(total_days)]
    s = Solver()
    
    # Each day must be a valid city
    for d in day:
        s.add(And(d >= 0, d < num_cities))
    
    # Flight transitions
    for i in range(total_days - 1):
        current = day[i]
        next_c = day[i+1]
        s.add(Or(
            current == next_c,
            Or([next_c == dest for dest in direct_flights[current]])
        ))
    
    # Total days per city
    for city in range(num_cities):
        s.add(Sum([If(day[i] == city, 1, 0) for i in range(total_days)]) == required_days[city])
    
    # Athens between day 1-6
    s.add(And([day[i] == Athens for i in range(6)]))
    
    # Naples between day 16-20
    s.add(And([day[i] == Naples for i in range(15, 20)]))
    
    if s.check() == sat:
        m = s.model()
        itinerary = []
        current = m[day[0]].as_long()
        start = 1
        
        for i in range(1, total_days):
            next_c = m[day[i]].as_long()
            if next_c != current:
                if start == i:
                    itinerary.append({'day_range': f'Day {start}', 'place': cities[current]})
                else:
                    itinerary.append({'day_range': f'Day {start}-{i}', 'place': cities[current]})
                itinerary.append({'day_range': f'Day {i}', 'place': cities[current]})
                itinerary.append({'day_range': f'Day {i}', 'place': cities[next_c]})
                start = i + 1
                current = next_c
        
        if start == total_days:
            itinerary.append({'day_range': f'Day {start}', 'place': cities[current]})
        else:
            itinerary.append({'day_range': f'Day {start}-{total_days}', 'place': cities[current]})
        
        return {'itinerary': itinerary}
    else:
        return None

result = solve_itinerary()
if result:
    import json
    print(json.dumps(result, indent=2))
else:
    print("No valid itinerary found.")