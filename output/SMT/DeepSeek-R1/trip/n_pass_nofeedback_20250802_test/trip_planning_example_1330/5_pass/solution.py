from z3 import *

def main():
    n_days = 25
    cities = ['Salzburg', 'Hamburg', 'Zurich', 'Nice', 'Venice', 'Copenhagen', 'Bucharest', 'Brussels', 'Naples']
    req = [2, 3, 4, 2, 4, 3, 3, 2, 2]
    city_index = {city: idx for idx, city in enumerate(cities)}
    
    # Enhanced graph with necessary connections
    graph = {
        'Salzburg': ['Zurich', 'Venice'],
        'Hamburg': ['Brussels', 'Copenhagen', 'Venice', 'Zurich'],
        'Zurich': ['Salzburg', 'Nice', 'Hamburg'],
        'Nice': ['Zurich'],
        'Venice': ['Salzburg', 'Naples', 'Bucharest', 'Hamburg'],
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
    for i in range(1, 24):
        s.add(c[i] != salzburg_idx)
    
    # Constraint: Exact day counts per city
    for k in range(len(cities)):
        s.add(Sum([If(c[i] == k, 1, 0) for i in range(n_days)]) == req[k])
    
    # Constraint: Valid transitions between days
    for i in range(n_days - 1):
        s.add(Or([And(c[i] == a, c[i+1] == b) for (a, b) in allowed_pairs]))
    
    # New constraint: Enforce consecutive stays
    for k in range(len(cities)):
        # Create a list that is 1 when in city k, 0 otherwise
        in_city = [If(c[i] == k, 1, 0) for i in range(n_days)]
        # Constraints for the start of a stay
        starts = []
        for i in range(n_days):
            # First day is start if we're in the city
            if i == 0:
                starts.append(in_city[i])
            else:
                # Current day is in city and previous day is not
                starts.append(And(in_city[i] == 1, in_city[i-1] == 0))
        # Constraints for the end of a stay
        ends = []
        for i in range(n_days):
            # Last day is end if we're in the city
            if i == n_days - 1:
                ends.append(in_city[i])
            else:
                # Current day is in city and next day is not
                ends.append(And(in_city[i] == 1, in_city[i+1] == 0))
        
        # The number of starts must equal the number of ends
        num_starts = Sum([If(starts[i], 1, 0) for i in range(n_days)])
        num_ends = Sum([If(ends[i], 1, 0) for i in range(n_days)])
        s.add(num_starts == num_ends)
        
        # For each start, there must be a corresponding end
        # This ensures consecutive blocks
        for i in range(n_days):
            for j in range(i, n_days):
                if j > i:
                    # If there's a start at i and end at j, then all days between must be in the city
                    s.add(Implies(And(starts[i], ends[j]),
                                  And([in_city[k] == 1 for k in range(i, j+1)])))
    
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