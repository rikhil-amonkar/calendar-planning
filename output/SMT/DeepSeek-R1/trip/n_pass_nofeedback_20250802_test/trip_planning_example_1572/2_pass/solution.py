from z3 import *

def main():
    cities_list = ['Berlin', 'Munich', 'Hamburg', 'Frankfurt', 'Cologne', 'Stuttgart', 'Paris', 'Lyon', 'Nice', 'Milan', 
                  'Rome', 'Naples', 'Barcelona', 'Madrid', 'Seville', 'Valencia', 'Athens', 'Budapest', 'Vienna', 'Prague', 
                  'Zurich', 'Geneva', 'Amsterdam', 'Brussels', 'Copenhagen', 'Stockholm', 'Helsinki', 'Oslo', 'Riga', 'Warsaw']
    
    n_stops = 11
    s = Solver()
    
    c = [Int(f'c_{i}') for i in range(n_stops)]
    d = [Int(f'd_{i}') for i in range(n_stops)]
    
    # Fix the first and last city to Berlin (index 0)
    s.add(c[0] == 0)
    s.add(c[10] == 0)
    
    # All city indices must be within the valid range
    for i in range(n_stops):
        s.add(c[i] >= 0, c[i] < len(cities_list))
    
    # Middle 9 cities must be distinct and not Berlin
    s.add(Distinct([c[i] for i in range(1, 10)]))
    for i in range(1, 10):
        s.add(c[i] != 0)
    
    # Consecutive cities must be different
    for i in range(0, 10):
        s.add(c[i] != c[i+1])
    
    # Each stay duration must be at least 1 day
    for i in range(n_stops):
        s.add(d[i] >= 1)
    
    # Sum of all stay durations must be 13
    s.add(Sum(d) == 13)
    
    if s.check() == sat:
        m = s.model()
        c_val = [m.evaluate(c[i]).as_long() for i in range(n_stops)]
        d_val = [m.evaluate(d[i]).as_long() for i in range(n_stops)]
        
        start_days = [1]
        for i in range(1, n_stops):
            start_days.append(start_days[i-1] + d_val[i-1] + 1)
        
        end_days = [start_days[i] + d_val[i] - 1 for i in range(n_stops)]
        
        itinerary = []
        for i in range(n_stops):
            start = start_days[i]
            end = end_days[i]
            if start == end:
                day_range_str = f"Day {start}"
            else:
                day_range_str = f"Day {start}-{end}"
            city_name = cities_list[c_val[i]]
            itinerary.append({'day_range': day_range_str, 'place': city_name})
        
        plan = {'itinerary': itinerary}
        print(f"Plan found: {plan}")
    else:
        print("No valid plan found")

if __name__ == "__main__":
    main()