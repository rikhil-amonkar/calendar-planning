from z3 import Solver, Int, Distinct, Or, And, sat
import sys

def main():
    s = Solver()
    
    # We have 5 cities for the middle segments. Map them to integers:
    # 0: Krakow, 1: Lisbon, 2: Munich, 3: Porto, 4: Split
    order = [Int(f'order_{i}') for i in range(5)]
    
    # Each order[i] must be between 0 and 4
    for i in range(5):
        s.add(order[i] >= 0, order[i] <= 4)
    s.add(Distinct(order))
    
    # Flight constraints: first city from Amsterdam must be in {Krakow, Munich, Split} -> {0,2,4}
    s.add(Or(order[0] == 0, order[0] == 2, order[0] == 4))
    # Last city to Amsterdam must be in {Krakow, Munich, Split} -> {0,2,4}
    s.add(Or(order[4] == 0, order[4] == 2, order[4] == 4))
    
    # Flight connections between consecutive middle cities
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
        # We'll create a condition that (c1, c2) is in the connections
        cond = Or(
            And(c1 == 0, Or(c2 == 1, c2 == 2, c2 == 3, c2 == 4)),
            And(c1 == 1, Or(c2 == 0, c2 == 2, c2 == 3)),
            And(c1 == 2, Or(c2 == 0, c2 == 1, c2 == 3, c2 == 4)),
            And(c1 == 3, Or(c2 == 0, c2 == 1, c2 == 2)),
            And(c1 == 4, Or(c2 == 0, c2 == 2))
        )
        s.add(cond)
    
    # Durations for the first 6 segments (first Amsterdam and then the 5 middle cities)
    durations = [Int(f'dur_{i}') for i in range(6)]
    # Each duration at least 2
    for d in durations:
        s.add(d >= 2)
    # Sum of these 6 durations must be 15 (because last segment is 1 day, total 16)
    s.add(sum(durations) == 15)
    
    # Check for a solution
    if s.check() == sat:
        m = s.model()
        # Get the order
        order_vals = [m.evaluate(order[i]).as_long() for i in range(5)]
        dur_vals = [m.evaluate(durations[i]).as_long() for i in range(6)]
        
        # Map integers to city names for the middle segments
        city_map = {
            0: 'Krakow',
            1: 'Lisbon',
            2: 'Munich',
            3: 'Porto',
            4: 'Split'
        }
        
        # Build the itinerary
        segments = []
        # First segment: Amsterdam
        start = 1
        end = dur_vals[0]
        segments.append({'day_range': f'Day {start}-{end}', 'place': 'Amsterdam'})
        
        current = end
        # Middle segments: 5 cities
        for i in range(5):
            city_index = order_vals[i]
            city_name = city_map[city_index]
            dur = dur_vals[1+i]
            seg_start = current + 1
            seg_end = current + dur
            segments.append({'day_range': f'Day {seg_start}-{seg_end}', 'place': city_name})
            current = seg_end
        
        # Last segment: Amsterdam for 1 day (day 16)
        segments.append({'day_range': 'Day 16', 'place': 'Amsterdam'})
        
        # Format the result
        plan = {'itinerary': segments}
        print(plan)
    else:
        print('No valid plan found', file=sys.stderr)
        exit(1)

if __name__ == '__main__':
    main()