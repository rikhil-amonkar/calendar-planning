from z3 import Solver, Int, Distinct, Or, And, If, sat, Sum
import sys

def main():
    s = Solver()
    
    # Middle cities: 0: Krakow, 1: Lisbon, 2: Munich, 3: Porto, 4: Split
    order = [Int(f'order_{i}') for i in range(5)]
    for i in range(5):
        s.add(order[i] >= 0, order[i] < 5)
    s.add(Distinct(order))
    
    # Durations
    dur_s1 = Int('dur_s1')  # First Amsterdam segment
    dur_middle = [Int(f'dur_m{i}') for i in range(5)]  # Middle cities
    dur_s7 = 1  # Last Amsterdam segment (fixed)
    
    # First Amsterdam must be at least 2 days
    s.add(dur_s1 >= 2)
    
    # Middle cities constraints: exactly one has 1 day, others >=2
    one_day_flags = []
    for i in range(5):
        flag = Int(f'flag_{i}')
        s.add(flag == If(dur_middle[i] == 1, 1, 0))
        s.add(Or(dur_middle[i] == 1, dur_middle[i] >= 2))
        one_day_flags.append(flag)
    s.add(Sum(one_day_flags) == 1)
    
    # Total days = 16
    s.add(dur_s1 + Sum(dur_middle) + dur_s7 == 16)
    
    # Flight connections from Amsterdam to first middle city
    s.add(Or(order[0] == 0, order[0] == 2, order[0] == 4))
    
    # Flight connections between middle cities
    connections = {
        0: [1, 2, 3, 4],  # Krakow
        1: [0, 2, 3],      # Lisbon
        2: [0, 1, 3, 4],   # Munich
        3: [0, 1, 2],      # Porto
        4: [0, 2]          # Split
    }
    for i in range(4):
        c1 = order[i]
        c2 = order[i+1]
        s.add(Or(
            And(c1 == 0, Or(c2 == 1, c2 == 2, c2 == 3, c2 == 4)),
            And(c1 == 1, Or(c2 == 0, c2 == 2, c2 == 3)),
            And(c1 == 2, Or(c2 == 0, c2 == 1, c2 == 3, c2 == 4)),
            And(c1 == 3, Or(c2 == 0, c2 == 1, c2 == 2)),
            And(c1 == 4, Or(c2 == 0, c2 == 2))
        ))
    
    # Flight from last middle city to Amsterdam
    s.add(Or(order[4] == 0, order[4] == 2, order[4] == 4))
    
    # Solve
    if s.check() == sat:
        m = s.model()
        # Get durations
        dur_s1_val = m.evaluate(dur_s1).as_long()
        dur_middle_vals = [m.evaluate(dur_middle[i]).as_long() for i in range(5)]
        order_vals = [m.evaluate(order[i]).as_long() for i in range(5)]
        
        # Map to city names
        city_map = {
            0: 'Krakow',
            1: 'Lisbon',
            2: 'Munich',
            3: 'Porto',
            4: 'Split'
        }
        middle_cities = [city_map[idx] for idx in order_vals]
        
        # Build itinerary
        segments = []
        current_day = 1
        
        # First Amsterdam segment
        end = current_day + dur_s1_val - 1
        segments.append({'day_range': f'Day {current_day}-{end}', 'place': 'Amsterdam'})
        current_day = end + 1
        
        # Middle cities
        for i in range(5):
            end = current_day + dur_middle_vals[i] - 1
            segments.append({'day_range': f'Day {current_day}-{end}', 'place': middle_cities[i]})
            current_day = end + 1
        
        # Last Amsterdam segment (day 16)
        segments.append({'day_range': f'Day 16', 'place': 'Amsterdam'})
        
        plan = {'itinerary': segments}
        print(plan)
    else:
        print('No valid plan found', file=sys.stderr)
        exit(1)

if __name__ == '__main__':
    main()