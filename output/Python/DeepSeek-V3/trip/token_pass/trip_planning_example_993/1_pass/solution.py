import json
import itertools

def solve():
    cities = ['Riga', 'Frankfurt', 'Amsterdam', 'Vilnius', 'London', 'Stockholm', 'Bucharest']
    short = {'Riga':'R', 'Frankfurt':'F', 'Amsterdam':'A', 'Vilnius':'V', 'London':'L', 'Stockholm':'S', 'Bucharest':'B'}
    days_req = {'R':2, 'F':3, 'A':2, 'V':5, 'L':2, 'S':3, 'B':4}
    
    # Direct flights
    flights = [
        ('London', 'Amsterdam'),
        ('Vilnius', 'Frankfurt'),
        ('Riga', 'Vilnius'),
        ('Riga', 'Stockholm'),
        ('London', 'Bucharest'),
        ('Amsterdam', 'Stockholm'),
        ('Amsterdam', 'Frankfurt'),
        ('Frankfurt', 'Stockholm'),
        ('Bucharest', 'Riga'),
        ('Amsterdam', 'Riga'),
        ('Amsterdam', 'Bucharest'),
        ('Riga', 'Frankfurt'),
        ('Bucharest', 'Frankfurt'),
        ('London', 'Frankfurt'),
        ('London', 'Stockholm'),
        ('Amsterdam', 'Vilnius')
    ]
    
    # Make undirected graph
    graph = {c: set() for c in cities}
    for a,b in flights:
        graph[a].add(b)
        graph[b].add(a)
    
    # Event constraints
    # Amsterdam between day 2 and 3 -> Amsterdam must include day 2 or day 3
    # Vilnius between day 7 and 11 -> Vilnius must include some day in 7..11
    # Stockholm between day 13 and 15 -> Stockholm must include some day in 13..15
    
    best_itinerary = None
    
    # Try all permutations of city order
    for perm in itertools.permutations(cities):
        # Check direct flights between consecutive cities
        valid_order = True
        for i in range(len(perm)-1):
            if perm[i+1] not in graph[perm[i]]:
                valid_order = False
                break
        if not valid_order:
            continue
        
        # Now assign days to each city
        # We need to allocate days_req for each city
        # We have 15 days, but city-days = 21, so 6 travel days (double-counted)
        # Let's try: assign each city a number of *full days* (days where it's the only city),
        # and travel days where it's counted for two cities.
        # Simpler: We can model as each city has a start day and end day (inclusive),
        # with end day = start day + length - 1, but travel days overlap.
        # Actually, let's model as: day d in city perm[i] if d in [start_i, end_i],
        # with start_{i+1} = end_i (same day travel).
        # Then length in days for city i = end_i - start_i + 1.
        # We need sum(length_i) = 21, and end_6 = 14 (since day 1 to 15, index 0..14)
        # start_0 = 0 (day1)
        
        # We need to choose end_i for i=0..5, start_i = end_{i-1} for i>0, start_0=0
        # end_i >= start_i, end_i integer 0..14
        # end_6 = 14
        # For each city perm[i], length_i = end_i - start_i + 1
        # We need length_i >= days_req[short[perm[i]]]? No, because travel days double count,
        # so length_i can be less than days_req if some days are double counted? Wait,
        # length_i is already counting double days (since start_{i+1}=end_i), so length_i
        # is exactly the number of days the city appears in itinerary.
        # So we must have length_i = days_req[short[perm[i]]].
        
        # Then: end_i = start_i + days_req[short[perm[i]]] - 1
        # start_{i+1} = end_i
        # So start_0 = 0
        # end_0 = days_req[short[perm[0]]] - 1
        # start_1 = end_0
        # end_1 = start_1 + days_req[short[perm[1]]] - 1
        # ...
        # end_6 must be 14.
        
        start = [0]*7
        end = [0]*7
        possible = True
        for i in range(7):
            if i>0:
                start[i] = end[i-1]
            req = days_req[short[perm[i]]]
            end[i] = start[i] + req - 1
            if end[i] > 14:
                possible = False
                break
        if not possible:
            continue
        if end[6] != 14:
            continue
        
        # Check event constraints
        # Amsterdam between day 2 and 3 -> Amsterdam must include day 2 or day 3 (1-indexed)
        # Our days are 0-indexed: day1 = index0, day2=index1, day3=index2
        amsterdam_index = perm.index('Amsterdam')
        if not (start[amsterdam_index] <= 1 <= end[amsterdam_index] or start[amsterdam_index] <= 2 <= end[amsterdam_index]):
            continue
        
        # Vilnius between day 7 and 11 -> index 6..10
        vilnius_index = perm.index('Vilnius')
        if not (start[vilnius_index] <= 10 and end[vilnius_index] >= 6):
            continue
        
        # Stockholm between day 13 and 15 -> index 12..14
        stockholm_index = perm.index('Stockholm')
        if not (start[stockholm_index] <= 14 and end[stockholm_index] >= 12):
            continue
        
        # Valid itinerary found
        itinerary = []
        for i in range(7):
            day_start = start[i] + 1
            day_end = end[i] + 1
            if day_start == day_end:
                day_range_str = f"Day {day_start}"
            else:
                day_range_str = f"Day {day_start}-{day_end}"
            itinerary.append({"day_range": day_range_str, "place": perm[i]})
        
        best_itinerary = itinerary
        break
    
    if best_itinerary is None:
        return {"error": "No valid itinerary found"}
    
    return {"itinerary": best_itinerary}

if __name__ == "__main__":
    result = solve()
    print(json.dumps(result, indent=2))