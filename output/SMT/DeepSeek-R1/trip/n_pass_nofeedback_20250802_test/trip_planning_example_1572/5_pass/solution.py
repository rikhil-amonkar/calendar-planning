from z3 import *

def main():
    cities_list = ['Berlin', 'Munich', 'Hamburg', 'Frankfurt', 'Cologne', 'Stuttgart', 'Paris', 'Lyon', 'Nice', 'Milan', 
                  'Rome', 'Naples', 'Barcelona', 'Madrid', 'Seville', 'Valencia', 'Athens', 'Budapest', 'Vienna', 'Prague', 
                  'Zurich', 'Geneva', 'Amsterdam', 'Brussels', 'Copenhagen', 'Stockholm', 'Helsinki', 'Oslo', 'Riga', 'Warsaw']
    
    n_stops = 11
    s = Solver()
    
    # City index variables for 11 stops
    c = [Int(f'c_{i}') for i in range(n_stops)]
    
    # First and last must be Berlin (index 0)
    s.add(c[0] == 0)
    s.add(c[10] == 0)
    
    # Valid city indices for all stops
    for i in range(n_stops):
        s.add(c[i] >= 0, c[i] < len(cities_list))
    
    # Middle 9 cities distinct and not Berlin
    s.add(Distinct([c[i] for i in range(1, 10)]))
    for i in range(1, 10):
        s.add(c[i] != 0)
    
    # Consecutive cities must be different
    for i in range(10):
        s.add(c[i] != c[i+1])
    
    # Stay duration variables
    d = [Int(f'd_{i}') for i in range(n_stops)]
    # First and last Berlin stays at least 2 days
    s.add(d[0] >= 2)
    s.add(d[10] >= 2)
    # Intermediate stays exactly 1 day
    for i in range(1, 10):
        s.add(d[i] == 1)
    
    # Total stay days = 13 (2+9*1+2)
    s.add(Sum(d) == 13)
    
    # Travel days: 10 days (between 11 stops)
    # Total days = stay days + travel days = 13 + 10 = 23
    
    # Compute start and end days for each stop
    start_day = [Int(f'start_{i}') for i in range(n_stops)]
    end_day = [Int(f'end_{i}') for i in range(n_stops)]
    
    # First stop starts on day 1
    s.add(start_day[0] == 1)
    s.add(end_day[0] == start_day[0] + d[0] - 1)
    
    # Subsequent stops start after previous end + travel day
    for i in range(1, n_stops):
        s.add(start_day[i] == end_day[i-1] + 1 + 1)  # +1 for travel day
        s.add(end_day[i] == start_day[i] + d[i] - 1)
    
    # Total trip must end on day 23
    s.add(end_day[10] == 23)
    
    if s.check() == sat:
        m = s.model()
        c_val = [m.evaluate(c[i]).as_long() for i in range(n_stops)]
        d_val = [m.evaluate(d[i]).as_long() for i in range(n_stops)]
        start_val = [m.evaluate(start_day[i]).as_long() for i in range(n_stops)]
        end_val = [m.evaluate(end_day[i]).as_long() for i in range(n_stops)]
        
        itinerary = []
        for i in range(n_stops):
            start = start_val[i]
            end = end_val[i]
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