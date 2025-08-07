from z3 import *

def main():
    cities_list = ['Berlin', 'Munich', 'Hamburg', 'Frankfurt', 'Cologne', 'Stuttgart', 'Paris', 'Lyon', 'Nice', 'Milan', 
                  'Rome', 'Naples', 'Barcelona', 'Madrid', 'Seville', 'Valencia', 'Athens', 'Budapest', 'Vienna', 'Prague', 
                  'Zurich', 'Geneva', 'Amsterdam', 'Brussels', 'Copenhagen', 'Stockholm', 'Helsinki', 'Oslo', 'Riga', 'Warsaw']
    
    n_stops = 11
    s = Solver()
    
    c = [Int(f'c_{i}') for i in range(n_stops)]
    
    # Fix first and last to Berlin (index 0)
    s.add(c[0] == 0)
    s.add(c[10] == 0)
    
    # Valid city indices
    for i in range(n_stops):
        s.add(c[i] >= 0, c[i] < len(cities_list))
    
    # Middle 9 cities distinct and non-Berlin
    s.add(Distinct([c[i] for i in range(1, 10)]))
    for i in range(1, 10):
        s.add(c[i] != 0)
    
    # Consecutive cities different
    for i in range(10):
        s.add(c[i] != c[i+1])
    
    # Duration constraints
    d = [Int(f'd_{i}') for i in range(n_stops)]
    # First and last Berlin stays >= 2 days
    s.add(d[0] >= 2)
    s.add(d[10] >= 2)
    # Intermediate stays exactly 1 day
    for i in range(1, 10):
        s.add(d[i] == 1)
    # Total stay days = 13
    s.add(Sum(d) == 13)
    
    if s.check() == sat:
        m = s.model()
        c_val = [m.evaluate(c[i]).as_long() for i in range(n_stops)]
        d_val = [m.evaluate(d[i]).as_long() for i in range(n_stops)]
        
        # Compute day ranges with travel days
        start_days = [1]
        # Each subsequent start = prev start + prev stay + travel day
        for i in range(1, n_stops):
            start_days.append(start_days[i-1] + d_val[i-1] + 1)
        
        end_days = [start_days[i] + d_val[i] - 1 for i in range(n_stops)]
        
        itinerary = []
        for i in range(n_stops):
            start = start_days[i]
            end = end_days[i]
            if start == end:
                day_range = f"Day {start}"
            else:
                day_range = f"Day {start}-{end}"
            itinerary.append({'day_range': day_range, 'place': cities_list[c_val[i]]})
        
        plan = {'itinerary': itinerary}
        print(f"Plan found: {plan}")
    else:
        print("No valid plan found")

if __name__ == "__main__":
    main()