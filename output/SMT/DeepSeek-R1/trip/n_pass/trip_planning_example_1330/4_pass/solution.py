from z3 import *

def main():
    n_days = 25
    cities = ['Salzburg', 'Hamburg', 'Zurich', 'Nice', 'Venice', 'Copenhagen', 'Bucharest', 'Brussels', 'Naples']
    req = [2, 3, 4, 2, 4, 3, 3, 2, 2]
    city_index = {city: idx for idx, city in enumerate(cities)}
    
    # Enhanced graph with additional connections
    graph = {
        'Salzburg': ['Zurich', 'Venice'],
        'Hamburg': ['Brussels', 'Copenhagen', 'Venice', 'Zurich'],  # Added Venice and Zurich
        'Zurich': ['Salzburg', 'Nice', 'Hamburg'],  # Added Hamburg
        'Nice': ['Zurich'],
        'Venice': ['Salzburg', 'Naples', 'Bucharest', 'Hamburg'],  # Added Hamburg
        'Copenhagen': ['Hamburg'],
        'Bucharest': ['Venice'],
        'Brussels': ['Hamburg'],
        'Naples': ['Venice']
    }
    
    allowed_pairs = set()
    for city, neighbors in graph.items():
        i = city_index[city]
        for nb in neighbors:
            j = city_index[nb]
            allowed_pairs.add((i, j))
            allowed_pairs.add((j, i))
    for i in range(len(cities)):
        allowed_pairs.add((i, i))
    
    s = Solver()
    c = [Int('c_%d' % i) for i in range(n_days)]
    
    # Constraint: Cities must be valid indices
    for i in range(n_days):
        s.add(c[i] >= 0, c[i] < len(cities))
    
    # Fixed start/end in Salzburg
    s.add(c[0] == city_index['Salzburg'])
    s.add(c[24] == city_index['Salzburg'])
    
    # Explicitly forbid Salzburg on days 2-24
    salzburg_idx = city_index['Salzburg']
    for i in range(1, 24):  # Days 2-24 (0-indexed positions 1-23)
        s.add(c[i] != salzburg_idx)
    
    # Constraint: Exact day counts per city
    for k in range(len(cities)):
        s.add(Sum([If(c[i] == k, 1, 0) for i in range(n_days)]) == req[k])
    
    # Constraint: Valid transitions between days
    for i in range(n_days - 1):
        s.add(Or([And(c[i] == a, c[i+1] == b) for (a, b) in allowed_pairs]))
    
    if s.check() == sat:
        m = s.model()
        assignment = [m.evaluate(c[i]).as_long() for i in range(n_days)]
        itinerary = []
        start_idx = 0
        current_city = assignment[0]
        for i in range(1, n_days):
            if assignment[i] != current_city:
                end_idx = i - 1
                start_day = start_idx + 1
                end_day = end_idx + 1
                if start_day == end_day:
                    day_range = f"Day {start_day}"
                else:
                    day_range = f"Day {start_day}-{end_day}"
                itinerary.append({'day_range': day_range, 'place': cities[current_city]})
                start_idx = i
                current_city = assignment[i]
        # Add last segment
        start_day = start_idx + 1
        end_day = n_days
        if start_day == end_day:
            day_range = f"Day {start_day}"
        else:
            day_range = f"Day {start_day}-{end_day}"
        itinerary.append({'day_range': day_range, 'place': cities[current_city]})
        
        print('itinerary =', itinerary)
    else:
        print("No valid itinerary found.")

if __name__ == '__main__':
    main()