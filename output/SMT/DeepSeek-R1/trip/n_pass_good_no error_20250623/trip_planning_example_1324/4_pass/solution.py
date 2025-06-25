from z3 import *
import json

def format_block(start, end, city):
    if start == end:
        return {"day_range": f"Day {start}", "place": city}
    else:
        return {"day_range": f"Day {start}-{end}", "place": city}

def format_single(day, city):
    return {"day_range": f"Day {day}", "place": city}

def main():
    cities = ["Venice", "Barcelona", "Copenhagen", "Lyon", "Reykjavik", "Dubrovnik", "Athens", "Tallinn", "Munich"]
    durs = [4, 3, 4, 4, 4, 5, 2, 5, 3]
    n = len(cities)
    
    flight_list = [
        ('Copenhagen', 'Athens'),
        ('Copenhagen', 'Dubrovnik'),
        ('Munich', 'Tallinn'),
        ('Copenhagen', 'Munich'),
        ('Venice', 'Munich'),
        ('Reykjavik', 'Athens'),
        ('Athens', 'Dubrovnik'),
        ('Venice', 'Athens'),
        ('Lyon', 'Barcelona'),
        ('Copenhagen', 'Reykjavik'),
        ('Reykjavik', 'Munich'),
        ('Athens', 'Munich'),
        ('Lyon', 'Munich'),
        ('Barcelona', 'Reykjavik'),
        ('Venice', 'Copenhagen'),
        ('Barcelona', 'Dubrovnik'),
        ('Lyon', 'Venice'),
        ('Dubrovnik', 'Munich'),
        ('Barcelona', 'Athens'),
        ('Copenhagen', 'Barcelona'),
        ('Venice', 'Barcelona'),
        ('Barcelona', 'Munich'),
        ('Barcelona', 'Tallinn'),
        ('Copenhagen', 'Tallinn')
    ]
    
    allowed_pairs = []
    for flight in flight_list:
        c1, c2 = flight
        idx1 = cities.index(c1)
        idx2 = cities.index(c2)
        allowed_pairs.append((idx1, idx2))
        allowed_pairs.append((idx2, idx1))
    
    s = Solver()
    
    seq = [ Int('seq_%d' % i) for i in range(n) ]
    for i in range(n):
        s.add(seq[i] >= 0)
        s.add(seq[i] < n)
        
    s.add(Distinct(seq))
    
    prefix = [ Int('prefix_%d' % i) for i in range(n) ]
    s.add(prefix[0] == 0)
    for i in range(1, n):
        s.add(prefix[i] == prefix[i-1] + durs[seq[i-1]] - 1)
    
    dub_index = cities.index("Dubrovnik")
    bcn_index = cities.index("Barcelona")
    cop_index = cities.index("Copenhagen")
    
    dub_constraints = []
    for i in range(n):
        dub_constraints.append( And(seq[i] == dub_index, prefix[i] == 15) )
    s.add(Or(dub_constraints))
    
    bcn_constraints = []
    for i in range(n):
        start_day = prefix[i] + 1
        bcn_constraints.append( And(seq[i] == bcn_index, start_day >= 8, start_day <= 12) )
    s.add(Or(bcn_constraints))
    
    cop_constraints = []
    for i in range(n):
        start_day = prefix[i] + 1
        cop_constraints.append( And(seq[i] == cop_index, start_day >= 4, start_day <= 10) )
    s.add(Or(cop_constraints))
    
    for i in range(n-1):
        constraints = []
        for (a, b) in allowed_pairs:
            constraints.append( And(seq[i] == a, seq[i+1] == b) )
        s.add(Or(constraints))
    
    s.add(prefix[n-1] + durs[seq[n-1]] == 26)
    
    for i in range(n):
        s.add(prefix[i] >= 0)
    
    if s.check() == sat:
        m = s.model()
        seq_val = [ m.evaluate(seq[i]).as_long() for i in range(n) ]
        prefix_val = [ m.evaluate(prefix[i]).as_long() for i in range(n) ]
        
        start_days = [0] * n
        end_days = [0] * n
        for i in range(n):
            start_days[i] = prefix_val[i] + 1
            end_days[i] = start_days[i] + durs[seq_val[i]] - 1
        
        events = []
        events.append(format_block(start_days[0], end_days[0], cities[seq_val[0]]))
        
        for i in range(n-1):
            travel_day = end_days[i]
            events.append(format_single(travel_day, cities[seq_val[i]]))
            events.append(format_single(travel_day, cities[seq_val[i+1]]))
            events.append(format_block(start_days[i+1], end_days[i+1], cities[seq_val[i+1]]))
        
        result = {"itinerary": events}
        print(json.dumps(result, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()