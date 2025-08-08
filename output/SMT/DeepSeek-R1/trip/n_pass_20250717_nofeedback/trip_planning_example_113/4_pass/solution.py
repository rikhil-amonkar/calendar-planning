from z3 import *

def main():
    s = Solver()
    
    # Define 13 variables: c0 to c12
    c = [Int('c%d' % i) for i in range(13)]
    
    # Each variable must be 0 (Milan), 1 (Seville), or 2 (Naples)
    for i in range(13):
        s.add(Or(c[i] == 0, c[i] == 1, c[i] == 2))
    
    # Start in Naples: end of day0, day1, day2 must be Naples (city 2)
    s.add(c[0] == 2)
    s.add(c[1] == 2)
    s.add(c[2] == 2)
    
    # Must be in Seville for days 9-12 (end of day9 to day12: c9, c10, c11, c12)
    s.add(c[9] == 1)
    s.add(c[10] == 1)
    s.add(c[11] == 1)
    s.add(c[12] == 1)
    
    # Flight constraints: only direct flights between Milan and Naples or Milan and Seville
    for i in range(0, 12):
        s.add(If(
            c[i] != c[i+1],
            Or(
                And(c[i] == 0, c[i+1] == 1),
                And(c[i] == 1, c[i+1] == 0),
                And(c[i] == 0, c[i+1] == 2),
                And(c[i] == 2, c[i+1] == 0)
            ),
            True  # if no flight, it's okay
        ))
    
    # Count days in each city for days 1 to 12 (c1 to c12)
    milan_days = Sum([If(c[i] == 0, 1, 0) for i in range(1, 13)])
    seville_days = Sum([If(c[i] == 1, 1, 0) for i in range(1, 13)])
    naples_days = Sum([If(c[i] == 2, 1, 0) for i in range(1, 13)])
    
    s.add(milan_days == 7)
    s.add(seville_days == 4)
    s.add(naples_days == 3)
    
    if s.check() == sat:
        model = s.model()
        c_ints = [model.evaluate(c[i]).as_long() for i in range(13)]
        
        # Group consecutive days with the same city from day1 to day12
        segments = []
        start_day = 1
        current_city = c_ints[1]  # city at end of day1
        for day in range(2, 13):  # from day2 to day12
            if c_ints[day] != current_city:
                segments.append((start_day, day-1, current_city))
                start_day = day
                current_city = c_ints[day]
        segments.append((start_day, 12, current_city))
        
        # Format the itinerary
        city_names = {0: "Milan", 1: "Seville", 2: "Naples"}
        itinerary = []
        for seg in segments:
            s_day, e_day, city_idx = seg
            if s_day == e_day:
                day_range = f"Day {s_day}"
            else:
                day_range = f"Day {s_day}-{e_day}"
            itinerary.append({'day_range': day_range, 'place': city_names[city_idx]})
        
        result = {'itinerary': itinerary}
        print(result)
    else:
        print("No solution found")

if __name__ == '__main__':
    main()