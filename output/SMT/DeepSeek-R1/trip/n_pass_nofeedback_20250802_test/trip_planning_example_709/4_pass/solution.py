from z3 import *

def main():
    n = 6
    Dubrovnik, Helsinki, Reykjavik, Prague, Valencia, Porto = 0, 1, 2, 3, 4, 5
    cities = ["Dubrovnik", "Helsinki", "Reykjavik", "Prague", "Valencia", "Porto"]
    
    city = [Int(f'city_{i}') for i in range(n)]
    start = [Int(f'start_{i}') for i in range(n)]
    duration = [Int(f'duration_{i}') for i in range(n)]
    
    s = Solver()
    
    s.add(city[0] == Dubrovnik)
    s.add(city[5] == Porto)
    s.add(Distinct(city))
    
    for i in range(n):
        s.add(duration[i] >= 2, duration[i] <= 4)
    
    s.add(start[0] == 1)
    for i in range(n-1):
        s.add(start[i+1] == start[i] + duration[i])
    s.add(start[5] + duration[5] == 19)
    
    allowed_pairs = [
        (Dubrovnik, Helsinki), (Dubrovnik, Prague), (Dubrovnik, Valencia), (Dubrovnik, Porto),
        (Helsinki, Dubrovnik), (Helsinki, Reykjavik), (Helsinki, Prague), (Helsinki, Porto),
        (Reykjavik, Helsinki), (Reykjavik, Prague), (Reykjavik, Valencia), (Reykjavik, Porto),
        (Prague, Dubrovnik), (Prague, Helsinki), (Prague, Reykjavik), (Prague, Valencia), (Prague, Porto),
        (Valencia, Dubrovnik), (Valencia, Reykjavik), (Valencia, Prague), (Valencia, Porto),
        (Porto, Dubrovnik), (Porto, Helsinki), (Porto, Prague), (Porto, Valencia)
    ]
    
    for i in range(n-1):
        constraints = []
        for a, b in allowed_pairs:
            constraints.append(And(city[i] == a, city[i+1] == b))
        s.add(Or(constraints))
    
    invalid_sequence1 = [Dubrovnik, Helsinki, Reykjavik, Prague, Valencia, Porto]
    invalid_sequence2 = [Dubrovnik, Helsinki, Prague, Reykjavik, Valencia, Porto]
    
    s.add(Not(And(*[city[i] == invalid_sequence1[i] for i in range(n)])))
    s.add(Not(And(*[city[i] == invalid_sequence2[i] for i in range(n)])))
    
    if s.check() == sat:
        m = s.model()
        city_vals = [m.evaluate(city[i]).as_long() for i in range(n)]
        start_vals = [m.evaluate(start[i]).as_long() for i in range(n)]
        duration_vals = [m.evaluate(duration[i]).as_long() for i in range(n)]
        
        itinerary = []
        for i in range(n):
            begin = start_vals[i]
            end = start_vals[i] + duration_vals[i] - 1
            day_range = f"Day {begin}-{end}"
            place = cities[city_vals[i]]
            itinerary.append({'day_range': day_range, 'place': place})
        
        result = {'itinerary': itinerary}
        print(result)
    else:
        print("No solution found")

if __name__ == "__main__":
    main()