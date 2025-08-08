from z3 import *

def main():
    City, (Reykjavik, Istanbul, Edinburgh, Oslo, Stuttgart, Bucharest) = EnumSort('City', [
        'Reykjavik',
        'Istanbul',
        'Edinburgh',
        'Oslo',
        'Stuttgart',
        'Bucharest'
    ])
    
    n_segments = 6
    seg_city = [Const(f'seg_city_{i}', City) for i in range(n_segments)]
    seg_days = [Int(f'seg_days_{i}') for i in range(n_segments)]
    starts = [Int(f'starts_{i}') for i in range(n_segments)]
    
    s = Solver()
    
    allowed_flights = [
        (Bucharest, Oslo), (Oslo, Bucharest),
        (Istanbul, Oslo), (Oslo, Istanbul),
        (Reykjavik, Stuttgart), (Stuttgart, Reykjavik),
        (Bucharest, Istanbul), (Istanbul, Bucharest),
        (Stuttgart, Edinburgh), (Edinburgh, Stuttgart),
        (Istanbul, Edinburgh), (Edinburgh, Istanbul),
        (Oslo, Reykjavik), (Reykjavik, Oslo),
        (Istanbul, Stuttgart), (Stuttgart, Istanbul),
        (Oslo, Edinburgh), (Edinburgh, Oslo)
    ]
    
    # Cities must be distinct
    s.add(Distinct(seg_city))
    
    # Each segment must have at least 1 day
    for i in range(n_segments):
        s.add(seg_days[i] >= 1)
    
    # Total days = 19
    s.add(Sum(seg_days) == 19)
    
    # Define segment start days
    s.add(starts[0] == 1)
    for i in range(1, n_segments):
        s.add(starts[i] == starts[i-1] + seg_days[i-1])
    
    # Flight connections between consecutive segments
    for i in range(n_segments - 1):
        s.add(Or([And(seg_city[i] == a, seg_city[i+1] == b) for (a, b) in allowed_flights]))
    
    # Total days per city
    req_days = {
        Reykjavik: 5,
        Istanbul: 4,
        Edinburgh: 5,
        Oslo: 2,
        Stuttgart: 3,
        Bucharest: 5
    }
    for city, req in req_days.items():
        total = 0
        for i in range(n_segments):
            total += If(seg_city[i] == city, seg_days[i], 0)
        s.add(total == req)
    
    # Create overnight stay array (c[0]=day1, ..., c[18]=day19)
    c = []
    for day in range(1, 20):  # day from 1 to 19
        expr = None
        for seg_i in range(n_segments):
            in_seg = And(starts[seg_i] <= day, day < starts[seg_i] + seg_days[seg_i])
            if expr is None:
                expr = If(in_seg, seg_city[seg_i], Reykjavik)  # default doesn't matter
            else:
                expr = If(in_seg, seg_city[seg_i], expr)
        c.append(expr)
    
    # Istanbul must be visited on days 5-8
    s.add(Or(c[3] == Istanbul, c[4] == Istanbul))  # Day5
    s.add(Or(c[4] == Istanbul, c[5] == Istanbul))  # Day6
    s.add(Or(c[5] == Istanbul, c[6] == Istanbul))  # Day7
    s.add(Or(c[6] == Istanbul, c[7] == Istanbul))  # Day8
    
    # Oslo must be visited on days 8-9
    s.add(Or(c[6] == Oslo, c[7] == Oslo))  # Day8
    s.add(Or(c[7] == Oslo, c[8] == Oslo))  # Day9
    
    if s.check() == sat:
        m = s.model()
        seg_city_vals = [m.evaluate(seg_city[i]) for i in range(n_segments)]
        seg_days_vals = [m.evaluate(seg_days[i]).as_long() for i in range(n_segments)]
        
        current_start = 1
        itinerary = []
        for i in range(n_segments):
            days = seg_days_vals[i]
            end_day = current_start + days - 1
            if current_start == end_day:
                day_range = f"Day {current_start}"
            else:
                day_range = f"Day {current_start}-{end_day}"
            itinerary.append({
                'day_range': day_range,
                'place': str(seg_city_vals[i])
            })
            current_start = end_day + 1
        
        result = {'itinerary': itinerary}
        print(result)
    else:
        print("No solution found")

if __name__ == "__main__":
    main()