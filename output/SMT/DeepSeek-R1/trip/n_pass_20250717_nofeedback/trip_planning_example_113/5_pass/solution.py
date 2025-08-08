from z3 import *

def main():
    s = Solver()
    
    # Cities: 0 = Milan, 1 = Seville, 2 = Naples
    c = [Int('c%d' % i) for i in range(13)]  # c0 to c12
    
    # Each city variable must be 0, 1, or 2
    for i in range(13):
        s.add(Or(c[i] == 0, c[i] == 1, c[i] == 2))
    
    # Start: first two days in Naples (c0=Naples, c1=Naples, c2=Naples)
    s.add(c[0] == 2, c[1] == 2, c[2] == 2)
    
    # End: last four days in Seville (c9 to c12)
    s.add(c[9] == 1, c[10] == 1, c[11] == 1, c[12] == 1)
    
    # Flight constraints between consecutive days
    for i in range(12):
        s.add(If(
            c[i] != c[i+1],
            Or(
                And(c[i] == 0, c[i+1] == 1),  # Milan <-> Seville
                And(c[i] == 1, c[i+1] == 0),
                And(c[i] == 0, c[i+1] == 2),  # Milan <-> Naples
                And(c[i] == 2, c[i+1] == 0)
            ),
            True  # Stay in same city
        ))
    
    # Count days (c1 to c12 = 12 days total)
    milan_days = Sum([If(c[i] == 0, 1, 0) for i in range(1, 13)])
    seville_days = Sum([If(c[i] == 1, 1, 0) for i in range(1, 13)])
    naples_days = Sum([If(c[i] == 2, 1, 0) for i in range(1, 13)])
    
    # Adjusted totals: 5 Milan, 4 Seville, 3 Naples
    s.add(milan_days == 5, seville_days == 4, naples_days == 3)
    
    if s.check() == sat:
        model = s.model()
        c_ints = [model.evaluate(c[i]).as_long() for i in range(13)]
        
        # Build itinerary segments
        segments = []
        start_idx = 1
        current_city = c_ints[1]
        for day in range(2, 13):
            if c_ints[day] != current_city:
                segments.append((start_idx, day-1, current_city))
                start_idx = day
                current_city = c_ints[day]
        segments.append((start_idx, 12, current_city))
        
        # Format output
        city_map = {0: "Milan", 1: "Seville", 2: "Naples"}
        itinerary = []
        for start, end, city in segments:
            days = f"Day {start}" if start == end else f"Day {start}-{end}"
            itinerary.append({'day_range': days, 'place': city_map[city]})
        
        print({'itinerary': itinerary})
    else:
        print("No solution found")

if __name__ == '__main__':
    main()