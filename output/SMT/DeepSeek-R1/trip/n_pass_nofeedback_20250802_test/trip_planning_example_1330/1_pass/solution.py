from z3 import *
import json

def main():
    # Cities for the first 7 segments and their durations
    cities = ['Salzburg', 'Venice', 'Bucharest', 'Hamburg', 'Copenhagen', 'Nice', 'Zurich']
    durations = [2, 5, 4, 4, 4, 3, 5]
    
    # Mapping of city names to integers
    city_map = {
        'Salzburg': 0,
        'Venice': 1,
        'Bucharest': 2,
        'Hamburg': 3,
        'Copenhagen': 4,
        'Nice': 5,
        'Zurich': 6,
        'Brussels': 7
    }
    
    # Flight connections (as a list of tuples)
    flight_list = [
        ("Zurich", "Brussels"),
        ("Bucharest", "Copenhagen"),
        ("Venice", "Brussels"),
        ("Nice", "Zurich"),
        ("Hamburg", "Nice"),
        ("Zurich", "Naples"),
        ("Hamburg", "Bucharest"),
        ("Zurich", "Copenhagen"),
        ("Bucharest", "Brussels"),
        ("Hamburg", "Brussels"),
        ("Venice", "Naples"),
        ("Venice", "Copenhagen"),
        ("Bucharest", "Naples"),
        ("Hamburg", "Copenhagen"),
        ("Venice", "Zurich"),
        ("Nice", "Brussels"),
        ("Hamburg", "Venice"),
        ("Copenhagen", "Naples"),
        ("Nice", "Naples"),
        ("Hamburg", "Zurich"),
        ("Salzburg", "Hamburg"),
        ("Zurich", "Bucharest"),
        ("Brussels", "Naples"),
        ("Copenhagen", "Brussels"),
        ("Venice", "Nice"),
        ("Nice", "Copenhagen")
    ]
    
    # Build a connection matrix (8x8 for cities 0-7)
    n = 8  # cities 0 to 7
    connected = [[False] * n for _ in range(n)]
    for a, b in flight_list:
        if a in city_map and b in city_map:
            i = city_map[a]
            j = city_map[b]
            connected[i][j] = True
            connected[j][i] = True
    
    # Create the Z3 solver and variables
    s = Solver()
    perm = [Int('perm%d' % i) for i in range(7)]
    
    # Each perm[i] is between 0 and 6
    for p in perm:
        s.add(p >= 0, p <= 6)
    s.add(Distinct(perm))
    
    # Start days for segments 0 to 7 (segment0 to segment6, then segment7 starts at 21)
    s_days = [1]  # s0 = 1
    for i in range(7):
        dur_i = Int('dur_%d' % i)
        # dur_i equals the duration of the city at perm[i]
        cases = []
        for idx, d in enumerate(durations):
            cases.append(And(perm[i] == idx, dur_i == d))
        s.add(Or(cases))
        next_s = s_days[i] + dur_i - 1
        s_days.append(next_s)
    
    # The start of segment8 (Brussels) must be 21
    s.add(s_days[7] == 21)
    
    # Event constraints: Copenhagen and Nice
    for i in range(7):
        # For Copenhagen (index4): start day in [15,18]
        s.add(If(perm[i] == 4, And(s_days[i] >= 15, s_days[i] <= 18), True))
        # For Nice (index5): start day in [7,11]
        s.add(If(perm[i] == 5, And(s_days[i] >= 7, s_days[i] <= 11), True))
    
    # Flight constraints between consecutive segments (for the first 7 segments)
    # Precompute allowed_pairs for flights between the 7 cities (0-6) and to Brussels (7)
    allowed_pairs = []
    for a in range(7):
        for b in range(7):
            if connected[a][b]:
                allowed_pairs.append((a, b))
    
    # For segments0 to 5: flight from segment i to i+1
    for i in range(6):
        conds = []
        for a, b in allowed_pairs:
            conds.append(And(perm[i] == a, perm[i+1] == b))
        s.add(Or(conds))
    
    # Flight from segment6 (last of the first 7) to Brussels (7)
    conds_last = []
    for a in range(7):
        if connected[a][7]:
            conds_last.append(perm[6] == a)
    s.add(Or(conds_last))
    
    # Check and get the model
    if s.check() == sat:
        model = s.model()
        perm_val = [model.evaluate(perm[i]).as_long() for i in range(7)]
        s_days_val = [1]
        for i in range(7):
            city_idx = perm_val[i]
            dur = durations[city_idx]
            next_day = s_days_val[-1] + dur - 1
            s_days_val.append(next_day)
        
        # Build the segments: first 7 segments
        segments = []
        for i in range(7):
            start = s_days_val[i]
            end = s_days_val[i+1]
            city = cities[perm_val[i]]
            segments.append((start, end, city))
        # Add Brussels and Naples
        segments.append((21, 22, 'Brussels'))
        segments.append((22, 25, 'Naples'))
        
        # Build the itinerary for each day
        itinerary = []
        for day in range(1, 26):
            places = []
            for seg in segments:
                if day >= seg[0] and day <= seg[1]:
                    places.append(seg[2])
            itinerary.append({'day': day, 'place': places})
        
        # Output as JSON
        result = {'itinerary': itinerary}
        print(json.dumps(result))
    else:
        print("No solution found")

if __name__ == '__main__':
    main()