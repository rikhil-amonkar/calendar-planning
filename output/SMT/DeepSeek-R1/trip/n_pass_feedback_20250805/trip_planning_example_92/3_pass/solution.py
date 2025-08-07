from z3 import *

def main():
    s = Solver()
    days = 12
    # Create day assignments: 0=Dublin, 1=Riga, 2=Vilnius
    d = [Int(f'd_{i}') for i in range(days)]
    
    # Constraints
    # Day 1 must be Dublin (0)
    s.add(d[0] == 0)
    # Day 12 must be Vilnius (2)
    s.add(d[days-1] == 2)
    
    # At least 2 days in Riga (1)
    s.add(Sum([If(d[i] == 1, 1, 0) for i in range(days)]) >= 2)
    
    # Cities must appear in order: Dublin (0) -> Riga (1) -> Vilnius (2)
    # with no reversals (each day can stay same or increase by 1)
    for i in range(days-1):
        s.add(d[i+1] >= d[i])
        s.add(d[i+1] <= d[i] + 1)
    
    if s.check() == sat:
        m = s.model()
        assignment = [m.evaluate(d[i]).as_long() for i in range(days)]
        
        # Group consecutive days into segments
        segments = []
        current_city = assignment[0]
        start_day = 1
        
        def city_name(city_val):
            return {0: 'Dublin', 1: 'Riga', 2: 'Vilnius'}[city_val]
        
        for day in range(1, days):
            if assignment[day] != current_city:
                end_day = day
                # Format day range
                if start_day == end_day:
                    day_range = f"Day {start_day}"
                else:
                    day_range = f"Day {start_day}-{end_day}"
                segments.append({
                    'day_range': day_range,
                    'place': city_name(current_city)
                })
                # Reset for next segment
                current_city = assignment[day]
                start_day = day + 1
        
        # Add last segment
        if start_day == days:
            day_range = f"Day {days}"
        else:
            day_range = f"Day {start_day}-{days}"
        segments.append({
            'day_range': day_range,
            'place': city_name(current_city)
        })
        
        plan = {'itinerary': segments}
        print(f"Plan found: {plan}")
    else:
        print("No valid plan found")

if __name__ == "__main__":
    main()